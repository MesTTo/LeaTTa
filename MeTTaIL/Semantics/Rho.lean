/-
Module: MeTTaIL.Semantics.Rho
Layer: Semantics
Purpose: A rho-calculus target for the MeTTaIL-to-rho correspondence work. The syntax follows the
  `RhoCalc` surface used by `mettail-rust`: zero, drop, output, ordinary input, persistent input,
  parallel composition, and quoted processes as names. The reduction relation gives quote/drop, ordinary
  one-shot COMM, and persistent COMM on one channel. The RSpace
  section records the local `f1r3node` runtime boundary: produce and consume carry persistent flags,
  consume matches a list of payloads, and one matched consume produces a body with bound names filled.
  The K semantics in `f1r3node/rholang/src/main/k/rholang` splits that story into creation,
  matching, substitution, ordinary send/receive, persistent send, and persistent receive rules. This
  file models the ordinary and persistent one-channel receive cores, not the whole K machine.
  Parallel contexts and structural congruence are explicit so later compiler proofs can state whether
  they reason syntactically or modulo `|`.
Imports: MeTTaIL.Semantics.Denotational
Trusted boundary: none
Main exports: Rho.Name, Rho.Proc, Rho.substName, Rho.substProc, Rho.Step,
  Rho.StepModStruct, Rho.lts, Rho.RSpace, Rho.encodeAST, Rho.termLocation, Rho.tupleListener,
  Rho.listener_step, Rho.payloadForwarder, Rho.payloadForwarder_emits, Rho.drop_termLocation,
  Rho.receivedVar_drops
Open obligations: define the matcher/router process that sends matched GSLT redex bindings to listener
  channels, then prove the two-direction simulation with MeTTaIL reduction. The checked part here is the
  target calculus, the RSpace one-communication shape, and the listener firing facts that such a
  compiler uses.
-/
import MeTTaIL.Semantics.Denotational

namespace MeTTaIL
namespace Rho

mutual
  /-- A rho name: a source-level variable or the quote of a process. -/
  inductive Name where
    | var (ident : String)
    | quote (proc : Proc)

  /-- A rho process. `inputOnce` consumes one output; `input` is persistent and stays installed. -/
  inductive Proc where
    | zero
    | drop (name : Name)
    | out (chan : Name) (msg : Proc)
    | inputOnce (chan : Name) (binder : String) (body : Proc)
    | input (chan : Name) (binder : String) (body : Proc)
    | par (left right : Proc)
end

mutual
  /-- Substitute a name for a free name variable inside a rho name. -/
  def substName (x : String) (repl : Name) : Name → Name
    | .var y => if y == x then repl else .var y
    | .quote p => .quote (substProc x repl p)

  /-- Substitute a name for a free name variable inside a rho process. -/
  def substProc (x : String) (repl : Name) : Proc → Proc
    | .zero => .zero
    | .drop n => .drop (substName x repl n)
    | .out chan msg => .out (substName x repl chan) (substProc x repl msg)
    | .inputOnce chan binder body =>
        let chan' := substName x repl chan
        if binder == x then .inputOnce chan' binder body
        else .inputOnce chan' binder (substProc x repl body)
    | .input chan binder body =>
        let chan' := substName x repl chan
        if binder == x then .input chan' binder body else .input chan' binder (substProc x repl body)
    | .par left right => .par (substProc x repl left) (substProc x repl right)
end

/-- Right-associated parallel composition. -/
def parList : List Proc → Proc
  | [] => .zero
  | p :: ps => .par p (parList ps)

/-- One rho reduction step. Ordinary COMM consumes the input process. Persistent COMM keeps the input
    process, so compiled rewrite rules act as listeners. -/
inductive Step : Proc → Proc → Prop where
  | drop {p : Proc} : Step (.drop (.quote p)) p
  | comm_once {chan : Name} {binder : String} {body msg : Proc} :
      Step (.par (.inputOnce chan binder body) (.out chan msg))
        (substProc binder (.quote msg) body)
  | comm_once_symm {chan : Name} {binder : String} {body msg : Proc} :
      Step (.par (.out chan msg) (.inputOnce chan binder body))
        (substProc binder (.quote msg) body)
  | comm {chan : Name} {binder : String} {body msg : Proc} :
      Step (.par (.input chan binder body) (.out chan msg))
        (.par (.input chan binder body) (substProc binder (.quote msg) body))
  | comm_symm {chan : Name} {binder : String} {body msg : Proc} :
      Step (.par (.out chan msg) (.input chan binder body))
        (.par (.input chan binder body) (substProc binder (.quote msg) body))
  | par_left {p p' q : Proc} : Step p p' → Step (.par p q) (.par p' q)
  | par_right {p q q' : Proc} : Step q q' → Step (.par p q) (.par p q')
  | out_msg {chan : Name} {msg msg' : Proc} : Step msg msg' → Step (.out chan msg) (.out chan msg')

/-- Structural congruence for the parallel operator. Zero is the unit, and parallel is AC up to
    reassociation. -/
inductive StructEq : Proc → Proc → Prop where
  | refl {p : Proc} : StructEq p p
  | symm {p q : Proc} : StructEq p q → StructEq q p
  | trans {p q r : Proc} : StructEq p q → StructEq q r → StructEq p r
  | par_congr {p p' q q' : Proc} : StructEq p p' → StructEq q q' → StructEq (.par p q) (.par p' q')
  | par_comm {p q : Proc} : StructEq (.par p q) (.par q p)
  | par_assoc {p q r : Proc} : StructEq (.par (.par p q) r) (.par p (.par q r))
  | par_zero_left {p : Proc} : StructEq (.par .zero p) p
  | par_zero_right {p : Proc} : StructEq (.par p .zero) p

/-- Rho reduction modulo structural congruence. -/
def StepModStruct (p q : Proc) : Prop :=
  ∃ u v, StructEq p u ∧ Step u v ∧ StructEq v q

/-- Every syntactic rho step is a step modulo structural congruence. -/
theorem step_to_mod {p q : Proc} (h : Step p q) : StepModStruct p q :=
  ⟨p, q, .refl, h, .refl⟩

/-- The rho process calculus as an unlabelled transition system. -/
def lts : Denotational.LTS Proc Unit where
  step p _ q := StepModStruct p q

namespace RSpace

/-- Runtime payload sent on one RSpace channel. `persistent` mirrors the flag carried by f1r3node sends. -/
structure Produce where
  chan : Name
  data : List Proc
  persistent : Bool

/-- Runtime continuation waiting on one RSpace channel. The local f1r3node runtime supports joins;
    the one-channel form is the COMM case used by direct compiled rewrite listeners. -/
structure Consume where
  chan : Name
  binders : List String
  body : Proc
  persistent : Bool
  peek : Bool

/-- Substitute each received process, in order, into a waiting continuation. -/
def substPayload : Proc → List String → List Proc → Option Proc
  | body, [], [] => some body
  | body, binder :: binders, msg :: msgs =>
      substPayload (substProc binder (.quote msg) body) binders msgs
  | _, _, _ => none

/-- A consume matches a produce when the channel and payload arity agree. Pattern matching is left for
    the later `BindPattern` model; this checked fragment records the name-binding part of COMM. -/
def Fits (consume : Consume) (produce : Produce) (body : Proc) : Prop :=
  consume.chan = produce.chan ∧ substPayload consume.body consume.binders produce.data = some body

/-- One RSpace communication: a waiting continuation and a produced payload yield the substituted body. -/
inductive Comm : Consume → Produce → Proc → Prop where
  | mk {consume : Consume} {produce : Produce} {body : Proc} :
      Fits consume produce body → Comm consume produce body

/-- A one-binder consume receives one process by substituting its quoted payload into the body. -/
theorem fits_one (chan : Name) (binder : String) (body msg : Proc) (cp pp : Bool) :
    Fits { chan := chan, binders := [binder], body := body, persistent := cp, peek := false }
      { chan := chan, data := [msg], persistent := pp }
      (substProc binder (.quote msg) body) := by
  simp [Fits, substPayload]

/-- A one-binder RSpace communication is a rho COMM step in process form. -/
theorem comm_to_step_one (chan : Name) (binder : String) (body msg : Proc) (cp pp : Bool) :
    Comm { chan := chan, binders := [binder], body := body, persistent := cp, peek := false }
      { chan := chan, data := [msg], persistent := pp }
      (substProc binder (.quote msg) body) := by
  exact Comm.mk (fits_one chan binder body msg cp pp)

end RSpace

/-- A listener waits on `chan`, binds each name in order, then emits `target` on `outChan`. -/
def tupleListener (chan outChan : Name) : List String → Proc → Proc
  | [], target => .out outChan target
  | binder :: rest, target => .input chan binder (tupleListener chan outChan rest target)

/-- The first receive of a tuple listener fires by the rho COMM rule. -/
theorem tupleListener_step (chan outChan : Name) (binder : String) (rest : List String)
    (target msg : Proc) :
    Step (.par (tupleListener chan outChan (binder :: rest) target) (.out chan msg))
      (.par (tupleListener chan outChan (binder :: rest) target)
        (substProc binder (.quote msg) (tupleListener chan outChan rest target))) :=
  Step.comm

/-- A one-binder listener is the direct-rule shape used by the rho compiler prototype. -/
def listener (chan outChan : Name) (binder : String) (target : Proc) : Proc :=
  tupleListener chan outChan [binder] target

/-- A one-binder listener is persistent: after COMM, the same listener remains in parallel with the
    instantiated body. -/
theorem listener_step (chan outChan : Name) (binder : String) (target msg : Proc) :
    Step (.par (listener chan outChan binder target) (.out chan msg))
      (.par (listener chan outChan binder target)
        (substProc binder (.quote msg) (.out outChan target))) := by
  simpa [listener, tupleListener] using
    tupleListener_step chan outChan binder [] target msg

/-- A listener that forwards the received process to an output channel after dereferencing the received
    quote. -/
def payloadForwarder (chan outChan : Name) (binder : String) : Proc :=
  .input chan binder (.out outChan (.drop (.var binder)))

/-- A forwarding listener receives one payload and emits the payload process on the output channel. If
    the output channel mentions the binder, rho substitution affects the channel as well. -/
theorem payloadForwarder_emits (chan outChan : Name) (binder : String) (msg : Proc) :
    Relation.ReflTransGen Step (.par (payloadForwarder chan outChan binder) (.out chan msg))
      (.par (payloadForwarder chan outChan binder)
        (.out (substName binder (.quote msg) outChan) msg)) := by
  have hcomm :
      Step (.par (payloadForwarder chan outChan binder) (.out chan msg))
        (.par (payloadForwarder chan outChan binder)
          (.out (substName binder (.quote msg) outChan) (.drop (.quote msg)))) := by
    simpa [payloadForwarder, substProc, substName] using
      (Step.comm :
        Step (.par (.input chan binder (.out outChan (.drop (.var binder)))) (.out chan msg))
          (.par (.input chan binder (.out outChan (.drop (.var binder))))
            (substProc binder (.quote msg) (.out outChan (.drop (.var binder))))))
  have hdrop :
      Step
        (.par (payloadForwarder chan outChan binder)
          (.out (substName binder (.quote msg) outChan) (.drop (.quote msg))))
        (.par (payloadForwarder chan outChan binder)
          (.out (substName binder (.quote msg) outChan) msg)) :=
    Step.par_right (Step.out_msg Step.drop)
  exact (Relation.ReflTransGen.single hcomm).trans (Relation.ReflTransGen.single hdrop)

/-- Render a label as a stable channel fragment. -/
def labelKey : Label → String
  | .id name => "id:" ++ name
  | .wild => "wild"
  | .listE _ => "list-empty"
  | .listCons _ => "list-cons"
  | .listOne _ => "list-one"

/-- Constructor channel for an encoded MeTTaIL term. -/
def constructorChannel (label : Label) : Name :=
  .var ("ctor:" ++ labelKey label)

mutual
  /-- Encode a MeTTaIL term as a rho process. A pattern variable becomes a drop of the same name, so a
      COMM substitution of that name supplies the received process. -/
  def encodeAST : AST → Proc
    | .var (.base ident) => .drop (.var ident)
    | .var path => .drop (.var (pathKey path))
    | .sexp label args => .out (constructorChannel label) (encodeASTList args)
    | .subst body repl v =>
        .out (.var "ctor:subst") (parList [encodeAST body, encodeAST repl, .drop (.var (pathKey v))])

  /-- Encode a list of MeTTaIL terms as a parallel payload. -/
  def encodeASTList : List AST → Proc
    | [] => .zero
    | arg :: rest => .par (encodeAST arg) (encodeASTList rest)

  /-- Render a dotted path as a stable channel fragment. -/
  def pathKey : DottedPath → String
    | .base ident => ident
    | .qualified ident rest => ident ++ "." ++ pathKey rest
end

/-- The rho location name for a MeTTaIL term is the quote of its encoded process. -/
def termLocation (term : AST) : Name :=
  .quote (encodeAST term)

/-- Dropping a term location recovers the encoded MeTTaIL term. -/
theorem drop_termLocation (term : AST) :
    Step (.drop (termLocation term)) (encodeAST term) := by
  simp [termLocation]
  exact Step.drop

/-- A received process stored under a name variable can be recovered by dropping the substituted name. -/
theorem receivedVar_drops (binder : String) (msg : Proc) :
    Step (substProc binder (.quote msg) (.drop (.var binder))) msg := by
  simp [substProc, substName]
  exact Step.drop

end Rho
end MeTTaIL
