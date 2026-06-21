/-
Module: MettaHyperonFull.Operational.Semantics
Layer: Operational
Purpose: The small-step semantics of the four-register machine (arXiv:2305.17218 §3.3). Defines the
  one-step function `smallStep?` with its step kinds (QUERY, CHAIN, add/remove-atom, OUTPUT), the
  one-step reducer `reduceAtom` for atoms (equality rules, grounded operators, `if`/`let`/`match`/
  `transform`/`superpose`), and the fuel-bounded drivers `runFuel` and `run`. Input is drained
  first, then the workspace.
Imports: MettaHyperonFull.Operational.State, MettaHyperonFull.Core.Builtins
Trusted boundary: human-reviewed spec
Main exports: StepKind, equalityReductions, equalityStep, stepAddAtom, stepRemAtom, reduceAtom,
  reduceArgs, smallStep?, runFuel, run
Open obligations: `call-native` has no dispatch table here, so native-function atoms fall through to
  the equality-rule case; on fuel exhaustion, `runFuel` returns the state with no halt-versus-cutoff
  signal.
-/
import MettaHyperonFull.Operational.State
import MettaHyperonFull.Core.Builtins

namespace Metta

/-- Labels for the rules of the small-step semantics, one per transition. -/
inductive StepKind where
  | query | chain | addAtom | remAtom | output
  deriving Repr, BEq, Inhabited

/-- Find all equality-rule reductions of `a` in `space`. For each rule `(= lhs rhs)` in the space,
    each unifier of `lhs` against `a` produces one reduct `instantiate b rhs`. -/
def equalityReductions (space : Space) (a : Atom) : List Atom :=
  space.equalityRules.flatMap (fun p =>
    match matchAtoms p.fst a with
    | [] => []
    | bs => bs.map (fun b => instantiate b p.snd))

/-- Apply one `add-atom` step: consume the matched input command, insert `a` into the knowledge base,
    and write `()` to output. -/
def stepAddAtom (s : State) (call a : Atom) : State :=
  let st := { s with input := Space.removeOne s.input call }
  State.pushOutput (State.addKb st a) Atom.unit

/-- Apply one `remove-atom` step: consume the matched input command, delete one occurrence of `a` from
    the knowledge base, and write `()` to output. -/
def stepRemAtom (s : State) (call a : Atom) : State :=
  let st := { s with input := Space.removeOne s.input call }
  State.pushOutput (State.remKb st a) Atom.unit

/-- Return `some` of the equality-rule reductions of `a`, or `none` when no rule in `kb` matches. -/
def equalityStep (kb : Space) (a : Atom) : Option (List Atom) :=
  match equalityReductions kb a with
  | [] => none
  | reds => some reds

mutual

/-- Reduce `a` by one step against `kb` and the grounded builtins. Returns `none` when `a` is a
    normal form (insensitive to every rule, arXiv:2305.17218 §3.3).

    Priority order: space-aware queries (`transform`, `match`, `get-type`) fire first; `if` and
    `let` reduce the condition/value sub-expression before the whole form; `superpose` unfolds
    immediately; a grounded operator with `evalArgs` mode reduces arguments left-to-right before
    firing, so `(+ (* 2 3) 4)` evaluates correctly; equality rules `(= lhs rhs)` apply last.

    Limitation: `call-native` has no dispatch table here, so native-function atoms fall through to
    the equality-rule case and are returned unchanged if no rule matches. -/
def reduceAtom (cfg : RuntimeConfig) (kb : Space) : Atom → Option (List Atom)
  | Atom.expr [Atom.sym "transform", pattern, tmpl] => some (kb.transform pattern tmpl)
  | Atom.expr [Atom.sym "match", _, pattern, tmpl] => some (kb.transform pattern tmpl)
  | Atom.expr [Atom.sym "get-type", x] => some (kb.typeAssignments x)
  | Atom.expr [Atom.sym "if", c, t, e] =>
      match c with
      | Atom.gnd (Ground.bool true) => some [t]
      | Atom.sym "True" => some [t]
      | Atom.gnd (Ground.bool false) => some [e]
      | Atom.sym "False" => some [e]
      | _ =>
          match reduceAtom cfg kb c with
          | some cs => some (cs.map fun c' => Atom.expr [Atom.sym "if", c', t, e])
          | none => none
  | Atom.expr [Atom.sym "let", Atom.var x, v, body] =>
      match reduceAtom cfg kb v with
      | some vs => some (vs.map fun v' => Atom.expr [Atom.sym "let", Atom.var x, v', body])
      | none => some [Subst.apply [(x, v)] body]
  | Atom.expr [Atom.sym "superpose", Atom.expr xs] => some xs
  | Atom.expr (Atom.sym op :: args) =>
      let whole := Atom.expr (Atom.sym op :: args)
      match cfg.groundings.lookup op with
      | none => equalityStep kb whole
      | some g =>
          let applyOp : Option (List Atom) :=
            match g.impl args with
            | ReduceResult.ok rs => some rs
            | ReduceResult.runtimeError msg =>
                some [Atom.expr [Atom.sym "Error", whole, Atom.gnd (Ground.str msg)]]
            | _ => equalityStep kb whole
          match g.mode with
          | GroundMode.quoteArgs => applyOp
          | GroundMode.evalArgs =>
              match reduceArgs cfg kb args with
              | some argss => some (argss.map (fun args' => Atom.expr (Atom.sym op :: args')))
              | none => applyOp
  | a => equalityStep kb a

/-- Reduce the left-most reducible element of `args` by one step. Returns one updated argument list
    per nondeterministic result, or `none` when every element is already a normal form. -/
def reduceArgs (cfg : RuntimeConfig) (kb : Space) : List Atom → Option (List (List Atom))
  | [] => none
  | x :: xs =>
      match reduceAtom cfg kb x with
      | some rs => some (rs.map (fun r => r :: xs))
      | none =>
          match reduceArgs cfg kb xs with
          | some xss => some (xss.map (fun xs' => x :: xs'))
          | none => none

end

/-- One small step of the four-register machine (arXiv:2305.17218 §3.3). Returns `none` when both
    input and workspace are empty (the machine has halted).

    Input is drained first. `add-atom`/`remove-atom` mutate the knowledge base and emit `()` (rules
    `ADD`/`REM`). Any other input atom is reduced: its results enter the workspace (`QUERY`), or it
    moves directly to output if it is a normal form (`OUTPUT`).

    Once input is empty, the workspace is drained. Reducible workspace atoms are rewritten in place
    (`CHAIN`); normal forms move to output (`OUTPUT`).

    Note: `runFuel` applies this in a loop bounded by `cfg.fuel`. If fuel runs out before the
    workspace empties, the state is returned as-is with no signal that computation was cut short.
    Callers that need to distinguish "halted" from "fuel exhausted" must check `fuel` themselves. -/
def smallStep? (cfg : RuntimeConfig) (s : State) : Option (StepKind × State) :=
  match s.input.atoms with
  | a :: _ =>
    match a with
    | Atom.expr [Atom.sym "add-atom", x] =>
        some (StepKind.addAtom, stepAddAtom s (Atom.expr [Atom.sym "add-atom", x]) x)
    | Atom.expr [Atom.sym "addAtom", x] =>
        some (StepKind.addAtom, stepAddAtom s (Atom.expr [Atom.sym "addAtom", x]) x)
    | Atom.expr [Atom.sym "remove-atom", x] =>
        some (StepKind.remAtom, stepRemAtom s (Atom.expr [Atom.sym "remove-atom", x]) x)
    | Atom.expr [Atom.sym "remAtom", x] =>
        some (StepKind.remAtom, stepRemAtom s (Atom.expr [Atom.sym "remAtom", x]) x)
    | _ =>
        let s' := { s with input := Space.removeOne s.input a }
        match reduceAtom cfg s.kb a with
        | some reds => some (StepKind.query, reds.foldl State.pushWork s')
        | none => some (StepKind.output, State.pushOutput s' a)
  | [] =>
    match s.work.atoms with
    | [] => none
    | u :: _ =>
        let s' := { s with work := Space.removeOne s.work u }
        match reduceAtom cfg s.kb u with
        | some reds => some (StepKind.chain, reds.foldl State.pushWork s')
        | none => some (StepKind.output, State.pushOutput s' u)

def runFuel (cfg : RuntimeConfig) : Nat → State → State
  | 0, s => s
  | Nat.succ n, s =>
      match smallStep? cfg s with
      | none => s
      | some (k, s') => runFuel cfg n (State.trace s' (reprStr k) Atom.unit)

def run (cfg : RuntimeConfig) (s : State) : State := runFuel cfg cfg.fuel s

end Metta
