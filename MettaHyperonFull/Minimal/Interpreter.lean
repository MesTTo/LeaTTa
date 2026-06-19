import MettaHyperonFull.Core.Matching
import MettaHyperonFull.Core.Space
import MettaHyperonFull.Core.Builtins
import Std.Data.HashMap

/-!
# Minimal MeTTa interpreter

A faithful Lean re-implementation of Hyperon's "minimal MeTTa" interpreter
(`hyperon-experimental/lib/src/metta/interpreter.rs`): a continuation-passing,
nondeterministic stack machine over the minimal instruction set
`eval`, `chain`, `unify`, `cons-atom`, `decons-atom`, `function`/`return`,
`collapse-bind`, `superpose-bind`, `metta`, `context-space`.

The Rust implementation uses `Rc<RefCell<Stack>>` shared mutability and `fn`-pointer
return handlers. Here the stack is an immutable list of frames (head = top) and the
return handler is an explicit tag (`Ret`). One interpreter step (`interpretStack1`) is
total; the driver (`interpretFuel`) is bounded by fuel, since MeTTa programs may
legitimately fail to terminate.

This module implements the **full** minimal-MeTTa instruction set: `eval`/`evalc`, `chain`,
`function`/`return`, `unify`, `cons-atom`/`decons-atom`, `collapse-bind`/`superpose-bind`, `metta`,
`capture`, `context-space`, together with the embedded space/state/type operations (`new-space`,
`add-atom`, `match`, `get-type`, `bind!`, `import!`, …) and the type-directed evaluator.
-/

namespace Metta.Minimal
open Metta

/-- Tag identifying a frame's return handler (the Rust `ReturnHandler` fn-pointer). -/
inductive Ret where
  | none_
  | chain
  | function
  deriving Repr, BEq, Inhabited

/-- A stack frame: the atom being interpreted (or, when `fin`, the value being returned),
    its return handler, its variable scope, and whether it is a finished/return frame. -/
structure Frame where
  /-- The atom being interpreted, or, when `fin`, the value being returned to the parent frame. -/
  atom : Atom
  /-- This frame's return handler (the `Ret` tag deciding how its result is delivered upward). -/
  ret : Ret := Ret.none_
  /-- The frame's variable scope: rule-variables retained for cross-argument binding propagation. -/
  vars : List VarName := []
  /-- `true` once `atom` holds a finished/returned value rather than pending work. -/
  fin : Bool := false
  deriving Inhabited

/-- Interpreter stack: head is the current/top frame; the tail is the parent chain. -/
abbrev Stack := List Frame

/-- A work item: a stack together with the variable bindings accumulated so far. -/
structure Item where
  /-- The evaluation stack for this (one) nondeterministic branch. -/
  stack : Stack
  /-- The variable bindings accumulated so far on this branch. -/
  bnd : Bindings := []
  deriving Inhabited

/-- `NotReducible`, the result of evaluating something with no applicable rule. -/
def notReducibleA : Atom := Atom.sym "NotReducible"
/-- `Empty`, the result that removes an alternative from the nondeterministic plan. -/
def emptyA : Atom := Atom.sym "Empty"

/-- `(Error <atom> <message>)` with the message as a symbol (matching the interpreter ops). -/
def errAtom (a : Atom) (msg : String) : Atom := Atom.expr [Atom.sym "Error", a, Atom.sym msg]

/-- Variable scope copied from the top of `prev` (Rust `Stack::vars_copy`). -/
def varsCopy : Stack → List VarName
  | [] => []
  | f :: _ => f.vars

/-- Heads of the embedded (minimal-MeTTa) operations. -/
def isEmbeddedOp : Atom → Bool
  | Atom.expr (Atom.sym op :: _) =>
      ["eval", "evalc", "chain", "unify", "cons-atom", "decons-atom", "function",
       "collapse-bind", "superpose-bind", "metta", "metta-thread", "capture", "context-space", "match",
       "get-type", "get-type-space", "get-doc", "new-state", "get-state", "change-state!", "new-space",
       "new-mork-space", "fork-space", "add-atom", "remove-atom",
       "get-atoms", "bind!", "import!"].contains op
  | _ => false

/-- Push `atom` onto `prev`, expanding `chain`/`function`/`unify` into their frame shapes and
    descending into the nested sub-atom (Rust `atom_to_stack`). Structural on `atom`. -/
def atomToStack : Atom → Stack → Stack
  | a, prev =>
    match a with
    | Atom.expr [Atom.sym "chain", nested, Atom.var v, templ] =>
        atomToStack nested ({ atom := Atom.expr [Atom.sym "chain", nested, Atom.var v, templ],
                              ret := Ret.chain, vars := varsCopy prev } :: prev)
    | Atom.expr [Atom.sym "function", Atom.expr body] =>
        atomToStack (Atom.expr body) ({ atom := Atom.expr [Atom.sym "function", Atom.expr body],
                                        ret := Ret.function, vars := varsCopy prev } :: prev)
    | Atom.expr [Atom.sym "unify", ua, up, ut, ue] =>
        { atom := Atom.expr [Atom.sym "unify", ua, up, ut, ue], ret := Ret.none_ } :: prev
    | Atom.expr (Atom.sym "chain" :: _) =>
        { atom := errAtom a "chain: expected (chain <nested> (: <var> Variable) <templ>)", fin := true } :: prev
    | Atom.expr (Atom.sym "function" :: _) =>
        { atom := errAtom a "function: expected (function (: <body> Expression))", fin := true } :: prev
    | Atom.expr (Atom.sym "unify" :: _) =>
        { atom := errAtom a "unify: expected (unify <atom> <pattern> <then> <else>)", fin := true } :: prev
    | _ => { atom := a, vars := varsCopy prev } :: prev

/-- A finished/return frame carrying `a`, on top of `st`. -/
def finItem (st : Stack) (a : Atom) (b : Bindings) : Item := { stack := { atom := a, fin := true } :: st, bnd := b }

/-- Wrap one evaluation result (Rust `eval_result`): a `(function ...)` result opens a new
    function scope; any other result is finished. -/
def evalResult (prev : Stack) (r : Atom) (b : Bindings) : Item :=
  match r with
  | Atom.expr (Atom.sym "function" :: _) => { stack := atomToStack r prev, bnd := b }
  | _ => finItem prev r b

/-- A variable, or an expression whose head is (recursively) a variable. Such atoms are not
    reduced by the interpreter (Rust `is_variable_op`); otherwise a bare variable would match the
    left-hand side of every equality rule. -/
def isVariableHeaded : Atom → Bool
  | Atom.var _ => true
  | Atom.expr (h :: _) => isVariableHeaded h
  | _ => false

/-- The dispatch key of an atom: its head symbol (for an expression) or itself (for a symbol).
    Atoms with the same key are the only ones whose equality rules can match each other; this is
    first-argument indexing, the same trick PeTTa gets from Prolog's clause indexing. -/
def headKey : Atom → Option String
  | Atom.sym s => some s
  | Atom.expr (Atom.sym h :: _) => some h
  | _ => none

open Std in
/-- A precomputed evaluation environment: equality rules indexed by head key (`ruleIndex`) plus the
    rules whose left-hand side is not symbol-headed (`varRules`, always candidates), the declared
    argument types of operators (`sigs`, for type-directed evaluation), and the grounding table.
    Built once per knowledge base so the hot path never rescans the whole atom list. -/
structure MinEnv where
  /-- `=`-rules indexed by the head key of their left-hand side (first-argument rule indexing). -/
  ruleIndex : HashMap String (List (Atom × Atom))
  /-- `=`-rules whose LHS has no head key (variable- or non-symbol-headed); candidates for every query. -/
  varRules : List (Atom × Atom)
  /-- Declared arrow signatures per operator, consulted by `typeMismatch` for argument type-checking. -/
  sigs : HashMap String (List Atom)
  /-- The grounding table: implementations of the grounded (built-in) operations. -/
  gt : GroundingTable
  /-- The full atom list of the space (used by `match`, which queries all atoms, not just `=` rules). -/
  atoms : List Atom
  /-- Declared types of each symbol from `(: sym T)` atoms (arrow or not), for `get-type` / runtime
      type-checking. A symbol may have SEVERAL declared types (e.g. `(: Ten Nat)` and `(: Ten Int)`),
      so this maps to the full list, matching Hyperon's `get_atom_types : … → Vec<AtomType>`. -/
  types : HashMap String (List Atom)
  /-- Pre-read `import!` targets: each imported module name (`c2_spaces_kb`) mapped to the atoms parsed
      from its file. The file read is IO and happens once in the runner (`Main`); the `import!`
      instruction itself is pure and just looks the atoms up here. -/
  imports : HashMap String (List Atom)
  /-- Declared types of *expression* subjects, from `(: (e …) T)` atoms (e.g. `(: (A B) PairAB)`),
      kept apart from `types` (keyed by symbol). A direct declaration takes precedence over the type
      inferred for an application in `getTypes`. -/
  exprTypes : List (Atom × Atom)

/-- The `(= lhs rhs)` equality rules extracted from an atom list: the rules `ofAtomsGT` indexes by
    head key. Factored out as a named definition so the metatheory (`Proofs/IndexingComplete.lean`)
    can characterise the index against it (sharing a single match-elaboration). -/
def extractRules (atoms : List Atom) : List (Atom × Atom) :=
  atoms.filterMap fun x => match x with
    | Atom.expr [Atom.sym "=", lhs, rhs] => some (lhs, rhs)
    | _ => none

open Std in
/-- Build a `MinEnv` from a flat atom list and a grounding table: index `(= lhs rhs)` atoms by
    `headKey lhs` (preserving knowledge-base order within each bucket) and collect `(: op (-> …))`
    argument-type signatures. -/
def MinEnv.ofAtomsGT (atoms : List Atom) (gt : GroundingTable) : MinEnv :=
  let rules : List (Atom × Atom) := extractRules atoms
  -- Index the `=`-rules by head key in one pass (`alter`, appending each rule in knowledge-base
  -- order); the head-less rules form `varRules` below. A single pass that preserves KB order gives
  -- `ruleIndex.getD k` and `varRules` clean equational characterisations (`Proofs/IndexingComplete`).
  let idx := rules.foldl
    (fun (m : HashMap String (List (Atom × Atom))) lr =>
      match headKey lr.fst with
      | some k => m.alter k (fun cur => some ((cur.getD []) ++ [lr]))
      | none => m)
    HashMap.emptyWithCapacity
  let sigs := atoms.foldl (fun (m : HashMap String (List Atom)) x => match x with
    | Atom.expr [Atom.sym ":", Atom.sym op, Atom.expr (Atom.sym "->" :: ts)] => m.insert op ts
    | _ => m) HashMap.emptyWithCapacity
  let types := atoms.foldl (fun (m : HashMap String (List Atom)) x => match x with
    | Atom.expr [Atom.sym ":", Atom.sym s, t] => m.insert s (m.getD s [] ++ [t])
    | _ => m) HashMap.emptyWithCapacity
  let exprTypes := atoms.filterMap fun x => match x with
    | Atom.expr [Atom.sym ":", Atom.expr es, t] => some (Atom.expr es, t)
    | _ => none
  { ruleIndex := idx, varRules := rules.filter (fun lr => (headKey lr.fst).isNone),
    sigs := sigs, gt := gt, atoms := atoms, types := types,
    imports := HashMap.emptyWithCapacity, exprTypes := exprTypes }

/-- Candidate equality rules for `toEval`: those keyed by its head plus the non-symbol-headed ones. -/
def MinEnv.candidates (env : MinEnv) (toEval : Atom) : List (Atom × Atom) :=
  (match headKey toEval with | some k => env.ruleIndex.getD k [] | none => []) ++ env.varRules

open Std in
/-- A mutable evaluation world: named spaces (`add-atom`/`match`/`get-atoms`), state cells indexed by
    id (`new-state`/`get-state`/`change-state!`), and `bind!`-bound tokens. It is threaded through
    evaluation (state-in/state-out), sequenced through the nondeterministic folds so a mutation is
    visible to later steps and later top-level queries, the pure analogue of Hyperon's mutable
    `Rc<RefCell>` spaces. -/
structure World where
  /-- Named spaces (`new-space`/`add-atom`/`remove-atom`/`match`), keyed by handle name. -/
  spaces : HashMap String (List Atom)
  /-- Mutable state cells (`new-state`/`get-state`/`change-state!`), keyed by cell id. -/
  store : HashMap Nat Atom
  /-- `bind!`-bound tokens, mapping each token symbol to its value (e.g. a space handle). -/
  tokens : HashMap String Atom
  /-- Atoms imported into `&self` via `import!` (kept separate from the per-query `MinEnv.atoms` KB,
      which `evalSequential` rebuilds each step; threaded here so an `import! &self` is visible only to
      the queries that follow it, faithful to Hyperon's order-sensitive file processing). -/
  selfExtra : List Atom

open Std in
/-- The empty world: no named spaces, state cells, tokens, or `&self` extension. -/
def World.empty : World :=
  { spaces := HashMap.emptyWithCapacity, store := HashMap.emptyWithCapacity,
    tokens := HashMap.emptyWithCapacity, selfExtra := [] }

/-- Set state cell `id` to `v`. -/
def World.setStore (w : World) (id : Nat) (v : Atom) : World := { w with store := w.store.insert id v }
/-- Register a fresh empty named space. -/
def World.newSpace (w : World) (name : String) : World := { w with spaces := w.spaces.insert name [] }
/-- Append `atoms` to named space `name`, creating it if absent. -/
def World.appendSpace (w : World) (name : String) (atoms : List Atom) : World :=
  { w with spaces := w.spaces.alter name fun cur => some ((cur.getD []) ++ atoms) }
/-- Remove the first occurrence of `a` from named space `name`. -/
def World.eraseFromSpace (w : World) (name : String) (a : Atom) : World :=
  { w with spaces := w.spaces.alter name fun cur => some ((cur.getD []).erase a) }
/-- Append atoms to the runtime `&self` extension (`add-atom`/`import! &self`). -/
def World.appendSelf (w : World) (atoms : List Atom) : World := { w with selfExtra := w.selfExtra ++ atoms }
/-- Remove the first occurrence of `a` from the runtime `&self` extension. -/
def World.eraseSelf (w : World) (a : Atom) : World := { w with selfExtra := w.selfExtra.erase a }
/-- Bind token `t` to value `v`. -/
def World.bindTok (w : World) (t : String) (v : Atom) : World := { w with tokens := w.tokens.insert t v }

/-- Threaded interpreter state: the gensym `counter` (rule-variable freshening, and the source of
    fresh state-cell / space ids) together with the mutable `world`. Replaces the bare `Nat` counter
    that used to thread through the interpreter, so space/state effects ride alongside gensym. -/
structure St where
  /-- The gensym counter: source of fresh rule-variable suffixes and state-cell / space ids. -/
  counter : Nat
  /-- The mutable world (named spaces, state cells, tokens) threaded through evaluation. -/
  world : World

/-- The initial interpreter state: gensym counter at zero over an empty world. -/
def St.init : St := { counter := 0, world := World.empty }

/-- Advance the gensym counter, returning the old value (a fresh id) and the advanced state. -/
def St.fresh (st : St) : Nat × St := (st.counter, { st with counter := st.counter + 1 })

/-- Transform the mutable world inside the threaded state. -/
def St.mapWorld (st : St) (f : World → World) : St := { st with world := f st.world }

/-- Resolve a `bind!`-bound token (`&kb`, `&state-token`) to its value; other atoms are unchanged. -/
def resolveTok (w : World) (a : Atom) : Atom :=
  match a with
  | Atom.sym s => (w.tokens[s]?).getD a
  | _ => a

/-- A state-cell handle `(State <id>)`. -/
def stateHandle (id : Nat) : Atom := Atom.expr [Atom.sym "State", Atom.gnd (Ground.int (Int.ofNat id))]

/-- The cell id of a state handle (after token resolution), if it is one. -/
def stateId (w : World) (a : Atom) : Option Nat :=
  match resolveTok w a with
  | Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)] => some id.toNat
  | _ => none

/-- The space name a handle/token denotes: `&self` and any `&…` token resolve to a name string. -/
def spaceName (w : World) (a : Atom) : Option String :=
  match resolveTok w a with
  | Atom.sym s => some s
  | _ => none

/-- Replace each state handle `(State id)` by its cell's current contents (one hop; cell contents are
    themselves stored already-resolved, so a single deref is faithful). This is why two *distinct*
    cells holding equal values compare equal and match each other, exactly as in Hyperon's `State`
    `PartialEq`, which derefs the `Rc<RefCell>` and compares the wrapped atom, not cell identity.
    Structural on the atom, hence total. -/
def resolveStates (w : World) : Atom → Atom
  | Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)] =>
      match w.store[id.toNat]? with
      | some v => v
      | none => Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)]
  | Atom.expr xs => Atom.expr (xs.map (resolveStates w))
  | a => a

/-- Substitute every `bind!`-bound token by its value throughout an atom (Hyperon replaces tokens at
    parse time, so a token stands for its value wherever it appears, e.g. `&state-active` inside a
    `match` pattern). Structural, hence total. -/
def subTokens (w : World) : Atom → Atom
  | Atom.sym s => (w.tokens[s]?).getD (Atom.sym s)
  | Atom.expr xs => Atom.expr (xs.map (subTokens w))
  | a => a

/-- Rewrite each state handle `(State id)` to `(StateValue <contents>)`, carrying the cell's value as
    a sub-term so that the (structural) `getTypes` can type it as `(StateMonad <type of contents>)`
    without itself needing the world. Structural, hence total. -/
def wrapStates (w : World) : Atom → Atom
  | Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)] =>
      match w.store[id.toNat]? with
      | some v => Atom.expr [Atom.sym "StateValue", v]
      | none => Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)]
  | Atom.expr xs => Atom.expr (xs.map (wrapStates w))
  | a => a

/-- Prepare an atom for `getTypes`: substitute tokens, then mark state handles with their contents.
    After this the atom is world-free, so `getTypes` stays a plain structural function. -/
def typePrep (w : World) (a : Atom) : Atom := wrapStates w (subTokens w a)

/-- Candidate `=` rules for evaluating `toEval`, including those added to `&self` at runtime
    (`add-atom &self (= …)` / `import! &self`), which live in `world.selfExtra` rather than the
    precompiled `MinEnv.ruleIndex`. Runtime rules come *after* the static ones (knowledge-base order),
    and are filtered by head like the static index. -/
def candidatesW (env : MinEnv) (w : World) (toEval : Atom) : List (Atom × Atom) :=
  let extra := w.selfExtra.filterMap fun x => match x with
    | Atom.expr [Atom.sym "=", lhs, rhs] =>
        match headKey lhs, headKey toEval with
        | some k1, some k2 => if k1 == k2 then some (lhs, rhs) else none
        | none, _ => some (lhs, rhs)
        | _, _ => none
    | _ => none
  env.candidates toEval ++ extra

/-- Rename every variable of an equality rule to a fresh name tagged with `counter`, so that each
    application of a rule uses distinct variables. Without this, a recursive function would reuse
    the same variable names across recursion levels in a single binding thread and clash (Hyperon
    freshens rule variables via the atomspace query / `make_unique`). -/
def freshenRule (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  match Atom.vars lhs ++ Atom.vars rhs with
  | [] => (lhs, rhs)  -- ground rule (e.g. a data fact): nothing to rename
  | vs =>
      let sub : Subst := vs.map fun v => (v, Atom.var (v ++ "#" ++ toString counter))
      (Subst.apply sub lhs, Subst.apply sub rhs)

/-- Query the knowledge base for `(= to_eval $X)` and return each instantiated right-hand side
    with merged bindings (Rust `query`), threading the gensym `counter`. Falls back to
    `NotReducible` when nothing matches, and refuses to reduce variable-headed atoms. -/
def queryOp (env : MinEnv) (st : St) (prev : Stack) (toEval : Atom) (b : Bindings) : List Item × St :=
  if isVariableHeaded toEval then ([finItem prev notReducibleA b], st) else
  let (results, st') := (candidatesW env st.world toEval).foldl (fun (acc : List Item × St) p =>
    let (lhs', rhs') := freshenRule acc.2.counter p.fst p.snd
    let items := (matchAtoms lhs' toEval).flatMap fun mb =>
      (Bindings.merge b mb).filterMap fun m =>
        if Bindings.hasLoop m then none else some (evalResult prev (instantiate m rhs') m)
    (acc.1 ++ items, { acc.2 with counter := acc.2.counter + 1 })) ([], st)
  if results.isEmpty then ([finItem prev notReducibleA b], st') else (results, st')

/-- `(eval <atom>)` (Rust `eval`/`eval_impl`): apply bindings; execute a grounded operator, push a
    nested embedded op, or query the space for an equality rule. Threads the gensym `counter`. -/
def evalOp (env : MinEnv) (st : St) (prev : Stack) (x : Atom) (b : Bindings) : List Item × St :=
  let x' := instantiate b x
  match x' with
  | Atom.expr (Atom.sym op :: args) =>
      -- grounded ops (`==`, the `assert*` family, arithmetic, …) compare/operate on *values*, so each
      -- argument has its `bind!` tokens substituted and its state handles dereferenced to cell
      -- contents first; this is what makes `(== (new-state 1) (new-state 1))`, `assertEqual` on
      -- states, and comparisons through a state token (`(get-token)` → `&state-token`) compare by
      -- content. Embedded ops that need the handle itself (`get-state`, `change-state!`) take the
      -- `noReduce` path below with `x'` (tokens/handles intact), so they are unaffected.
      match callGrounded env.gt op (args.map (fun a => resolveStates st.world (subTokens st.world a))) with
      | ReduceResult.ok results =>
          -- an empty result set is *no results* (a dead nondeterministic branch), not the `Empty`
          -- atom, so `(superpose ())` contributes nothing, and `(if False _ (superpose ()))` drops
          -- its branch (e3). Ops yield the `Empty` atom explicitly (`ok [Empty]`) when they mean it.
          (results.map (fun r => evalResult prev r b), st)
      | ReduceResult.runtimeError msg => ([finItem prev (errAtom x' msg) b], st)
      | ReduceResult.incorrectArgument _ => ([finItem prev notReducibleA b], st)
      | ReduceResult.noReduce =>
          if isEmbeddedOp x' then ([{ stack := atomToStack x' prev, bnd := b }], st)
          else queryOp env st prev x' b
  | _ =>
      if isEmbeddedOp x' then ([{ stack := atomToStack x' prev, bnd := b }], st)
      else queryOp env st prev x' b

/-- `(unify <atom> <pattern> <then> <else>)` (Rust `unify`): the matches of `atom` against
    `pattern` each yield `then` under the merged bindings; if none match, `else`. -/
def unifyOp (prev : Stack) (a p t e : Atom) (b : Bindings) : List Item :=
  let ms := (matchAtoms a p).flatMap (fun mb =>
    (Bindings.merge b mb).filterMap (fun m =>
      if Bindings.hasLoop m then none else some (finItem prev (instantiate m t) m)))
  if ms.isEmpty then [finItem prev e b] else ms

/-- Is this item a finished final result (a single finished frame with no parent)? -/
def isFinal : Item → Bool
  | ⟨[f], _⟩ => f.fin
  | _ => false

/-- The result atom of a final item paired with its bindings. The bindings are retained so a
    sub-evaluation can propagate query-variable solutions (e.g. `$a = A`) to sibling expression
    elements (Hyperon threads these through its mutable stack; we thread them explicitly). -/
def finalPair : Item → Atom × Bindings
  | ⟨f :: _, b⟩ => (instantiate b f.atom, b)
  | ⟨[], _⟩ => (emptyA, [])

/-- An unfinished work item surfaced as a `StackOverflow` error of its in-progress atom, used when
    fuel runs out, so exhausted branches are reported, not silently dropped. -/
def exhaustedPair : Item → Atom × Bindings
  | ⟨f :: _, b⟩ => (Atom.expr [Atom.sym "Error", instantiate b f.atom, Atom.sym "StackOverflow"], b)
  | ⟨[], b⟩ => (emptyA, b)

/-- The result atom of a final item, with its bindings applied. -/
def finalAtom (it : Item) : Atom := (finalPair it).1

/-- Resolve an atom to a fixpoint under `b`: apply `instantiate` repeatedly until it stops changing
    (bounded by the number of bindings, which caps any chain length). A single `instantiate` is
    one-step, since `Subst.apply` looks a variable up once and does not chase `$x ← $y ← Plato`, so this
    is what collapses a transitive solution to its final value. Recursive backchaining needs it: in
    b2's `(deduce (Evaluation (human $x)))` the query variable `$x` is first bound to a *rule*
    variable (via the `Implication` match) that only resolves to the answer `Plato` deeper in the
    recursion, so `$x` reaches `Plato` only through the chain. -/
def resolveAtom (b : Bindings) : Nat → Atom → Atom
  | 0, a => a
  | n + 1, a => let a' := instantiate b a; if a' == a then a else resolveAtom b n a'

/-- Restrict a binding set to the *solutions* of `vars` (an argument's own query variables), so that
    the internal freshened variables of a sub-evaluation do not leak into the continuation. Each
    query variable is emitted bound directly to its fully-resolved value (`resolveAtom`): this drops
    the internal variables and collapses transitive chains, so one `instantiate` in the continuation
    suffices. Equalities between two query variables are retained. (Previously this merely *filtered*
    to bindings touching `vars`, which severed transitive chains through a dropped intermediate
    variable (the b2 recursive-backchaining failure). -/
def restrictBnd (vars : List VarName) (b : Bindings) : Bindings :=
  let solved := vars.filterMap fun x =>
    let v := resolveAtom b (b.length + 1) (Atom.var x)
    if v == Atom.var x then none else some (BindingRel.val x v)
  let eqs := b.filter fun r => match r with
    | BindingRel.eq x y => vars.contains x && vars.contains y
    | _ => false
  solved ++ eqs

/-- The variables still live in the continuation `prev` (instantiated under the current bindings):
    the enclosing scope a sub-evaluation should retain bindings for (Hyperon `apply_and_retain`).
    A query solution like `$a = A` propagates to a sibling only if `$a` occurs in the continuation;
    variables introduced *inside* the sub-evaluation (e.g. a `let` pattern) do not, so they are dropped. -/
def scopeVars (b : Bindings) (prev : Stack) : List VarName :=
  prev.flatMap fun f => Atom.vars (instantiate b f.atom)

/-- Emit one alternative of `superpose-bind`: take the atom out of a `(atom bindings)` pair. -/
def superposeItem (prev : Stack) (b : Bindings) : Atom → Item
  | Atom.expr (a :: _) => finItem prev a b
  | other => finItem prev other b

/-- Cartesian product of a list of result-lists (combines nondeterministic argument evaluations). -/
def cartesian {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (cartesian rest).map fun t => x :: t

/-- Which argument positions of `(op …)` to evaluate (type-directed evaluation, Hyperon `metta`): an
    argument is evaluated unless its declared type is `Atom`/`Variable`. With no declared signature
    every argument is evaluated; data and patterns reduce to themselves, so that is safe. -/
def argMask (env : MinEnv) (op : String) (arity : Nat) : List Bool :=
  match env.sigs.get? op with
  | some ts => (List.range arity).map fun i => match ts[i]? with
      | some t => t != Atom.sym "Atom" && t != Atom.sym "Variable" && t != Atom.sym "Expression"
      | none => true
  | none => List.replicate arity true

/-- Whether the head operator of `a` has declared return type `Atom`. Faithful to Hyperon's
    `metta_call`/`interpret_expression`: the result of applying such a function is left inert rather
    than re-evaluated, which is exactly what makes `(noeval (+ 1 2))` stay `(+ 1 2)` while
    `(id (noeval (+ 1 2)))`, where `id : (-> $t $t)` has a non-`Atom` return, reduces to `3`. -/
def returnsAtom (env : MinEnv) (a : Atom) : Bool :=
  match headKey a with
  | some op => ((env.sigs.get? op).bind (·.getLast?)) == some (Atom.sym "Atom")
  | none => false

/-- The declared/inferred types of an atom (Hyperon `get_atom_types`, returning all candidates).
    Grounded literals get their built-in type; a symbol gets its `(: s T)` declarations (possibly
    several, or `%Undefined%` if undeclared, as gradual typing allows); a `(StateValue …)` handle gets `(StateMonad …)`;
    an application `(f …)` gets each of `f`'s arrow return types, with type variables instantiated by
    unifying the parameter types against the arguments (parametric inference). `%Undefined%` is top. -/
def getTypes (env : MinEnv) : Atom → List Atom
  | Atom.gnd (Ground.int _) => [Atom.sym "Number"]
  | Atom.gnd (Ground.float _) => [Atom.sym "Number"]
  | Atom.gnd (Ground.str _) => [Atom.sym "String"]
  | Atom.gnd (Ground.bool _) => [Atom.sym "Bool"]
  | Atom.gnd _ => [Atom.sym "Grounded"]
  | Atom.var _ => [Atom.sym "%Undefined%"]
  | Atom.sym s => match env.types.getD s [] with | [] => [Atom.sym "%Undefined%"] | ts => ts
  | Atom.expr [Atom.sym "StateValue", v] =>
      -- a state handle (rewritten by `wrapStates` to carry its contents): its type is
      -- `(StateMonad <type of contents>)`, matching the `(: new-state (-> $t (StateMonad $t)))` sig.
      [Atom.expr [Atom.sym "StateMonad", ((getTypes env v).head?).getD (Atom.sym "%Undefined%")]]
  | Atom.expr (f :: args) =>
      -- a direct `(: (e …) T)` declaration wins over inference (e.g. `(: (A B) PairAB)`)…
      match env.exprTypes.filter (fun p => p.1 == Atom.expr (f :: args)) with
      | t :: ts => (t :: ts).map (·.2)
      | [] =>
      -- …otherwise an application's type is each arrow return type of its head, with type variables
      -- instantiated by unifying the declared parameter types against the arguments' types (parametric
      -- inference, e.g. `(new-state 2) : (StateMonad Number)`, `(Cons Z Nil) : (List Nat)`).
      let argTs := args.map (fun a => ((getTypes env a).head?).getD (Atom.sym "%Undefined%"))
      match (getTypes env f).filterMap (fun t => match t with
              | Atom.expr (Atom.sym "->" :: ts) =>
                  let ret := (ts.getLast?).getD (Atom.sym "%Undefined%")
                  let tb := ((ts.dropLast).zip argTs).foldl (fun (b : Bindings) pa =>
                    match (matchAtoms (instantiate b pa.1) pa.2).head? with
                    | some b' => ((Bindings.merge b b').head?).getD b
                    | none => b) []
                  some (instantiate tb ret)
              | _ => none) with
        | [] => [Atom.sym "%Undefined%"]
        | rs => rs
  | Atom.expr [] => [Atom.sym "%Undefined%"]

mutual
/-- Hyperon's `match_reducted_types` (`types.rs`): structural type unification in which
    `%Undefined%` is a wildcard **at every nesting depth** (Hyperon's `replace_undefined_types`
    deep-replaces each `%Undefined%`, and only `%Undefined%`, by a wildcard matcher before
    `match_atoms`). `Atom` is an ordinary symbol here (it is *not* deep-replaced); only the top-level
    `matchType` treats `Atom` as the gradual top. So `(List Atom)` accepts `(List %Undefined%)` (an
    untyped list, e.g. a backward chainer's `(List Atom)` environment fed `(Cons (: x T) …)`, but
    not `(List Number)`, exactly as Hyperon. Type variables still bind at the leaf via `matchAtoms`. -/
def matchReduced (tb : Bindings) (expected actual : Atom) : Option Bindings :=
  if expected == Atom.sym "%Undefined%" || actual == Atom.sym "%Undefined%"
  then some tb
  else match expected, actual with
    | Atom.expr es, Atom.expr acts => matchReducedList tb es acts
    | _, _ => ((matchAtoms expected actual).flatMap (Bindings.merge tb)).head?
/-- Pointwise, binding-threading companion of `matchReduced` for the children of two type
    expressions; lengths must agree. -/
def matchReducedList (tb : Bindings) : List Atom → List Atom → Option Bindings
  | [], [] => some tb
  | e :: es, a :: acts => match matchReduced tb e a with
      | some tb' => matchReducedList tb' es acts
      | none => none
  | _, _ => none
end

/-- Unify a parameter type with an actual type, threading type-variable bindings `tb` (Hyperon
    `match_types`, `interpreter.rs:1221`). The gradual top matches immediately and leaves the bindings
    untouched: `%Undefined%` *or* `Atom` on **either** side (Hyperon checks `type1 == ATOM_TYPE_ATOM
    || type2 == ATOM_TYPE_ATOM`, lines 1224–1225, so a value of meta-type `Atom`, e.g. a quoted /
    unevaluated argument, is accepted against any parameter type and vice-versa). Otherwise it is the
    structural `match_reducted_types` (`matchReduced`), under which a *nested* `%Undefined%` is still a
    wildcard (but nested `Atom` is an ordinary symbol; only `%Undefined%` is deep-replaced), so type
    variables (`$t`, `(List $a)`) bind and parametric/dependent signatures stay consistent across the
    arrow's arguments. The gradual-top behaviour is Siek–Taha *consistency*, reflexive and symmetric
    but not transitive; `Proofs/Gradual.lean` proves both the relation (`Consistent.not_transitive`) and
    that this very function inherits it (`matchType_not_transitive`: `Number ~ %Undefined% ~ String`,
    yet `matchType … Number String = none`). -/
def matchType (tb : Bindings) (expected actual : Atom) : Option Bindings :=
  if expected == Atom.sym "%Undefined%" || actual == Atom.sym "%Undefined%"
     || expected == Atom.sym "Atom" || actual == Atom.sym "Atom"
  then some tb
  else matchReduced tb expected actual

/-- Type-check arguments against parameter types `argTypes`, threading type-variable bindings so that
    e.g. `(-> $t $t …)` forces both arguments to the same type and `(List $a)` matches by constructor.
    An argument is well-typed if ANY of its declared types unifies (so `Ten : {Nat, Int}` satisfies a
    `Nat` parameter). Returns the first `(position, expected, actual)` mismatch, or `none`. -/
def typeCheckArgs (env : MinEnv) (w : World) (argTypes : List Atom) : Nat → Bindings → List Atom → Option (Nat × Atom × Atom)
  | _, _, [] => none
  | i, tb, ai :: more =>
      match argTypes[i]? with
      | none => none  -- more arguments than declared parameters: stop (gradual)
      | some ti0 =>
          let ti := instantiate tb ti0
          let actuals := getTypes env (typePrep w ai)
          match actuals.findSome? (fun act => (matchType tb ti act).map (Prod.mk act)) with
          | some (_, tb') => typeCheckArgs env w argTypes (i + 1) tb' more
          | none => some (i + 1, ti, (actuals.head?).getD (Atom.sym "%Undefined%"))

/-- Runtime argument type-check for `(op a1 … an)` (Hyperon `check_if_function_type_is_applicable`):
    if `op` has a declared arrow type `(-> T1 … Tn R)`, return the first mismatching argument position
    with its (instantiated) expected and actual types, else `none`. Undeclared operators are not
    checked (gradual typing). -/
def typeMismatch (env : MinEnv) (w : World) (op : String) (args : List Atom) : Option (Nat × Atom × Atom) :=
  match env.sigs.get? op with
  | none => none
  | some ts => typeCheckArgs env w ts.dropLast 0 [] args

/-- Conjunctively match a list of patterns over the atoms of a space, threading the binding sets of
    earlier conjuncts into later ones (Hyperon's `(match S (, p1 … pk) tmpl)`). Each atom is freshened
    so its variables cannot capture query variables. Returns the surviving solution bindings and the
    advanced gensym counter. With a single pattern this is the ordinary `match`. -/
def matchConj (atoms : List Atom) : List Atom → St → List Bindings → (List Bindings × St)
  | [], st, sols => (sols, st)
  | p :: ps, st, sols =>
      let (sols', st') := sols.foldl (fun (acc : List Bindings × St) b =>
        -- Thread the bindings of earlier conjuncts into this pattern, so a query variable already
        -- pinned by a previous conjunct (e.g. `$x = Sam` from `(Frog $x)`) is substituted *before*
        -- matching. Otherwise it would re-bind against a freshened stored variable (`$x ↦ $x#k`)
        -- with no link back to its value, leaking spurious un-instantiated solutions (a3).
        let pInst := instantiate b p
        let (ext, st2) := atoms.foldl (fun (a2 : List Bindings × St) atom =>
          let atom' := (freshenRule a2.2.counter atom atom).1
          let more := (matchAtoms pInst atom').flatMap fun mb =>
            (Bindings.merge b mb).filter (fun m => !Bindings.hasLoop m)
          (a2.1 ++ more, { a2.2 with counter := a2.2.counter + 1 })) ([], acc.2)
        (acc.1 ++ ext, st2)) ([], st)
      matchConj atoms ps st' sols'

/-- Build the `@doc-formal` documentation for `atom` from the `(@doc atom …)` facts in the space and
    `atom`'s declared type, or `Empty` if undocumented (Hyperon's `get-doc`, g1_docs). A 3-element
    `(@doc a (@desc …))` is an atom-kind entry; a 5-element
    `(@doc a (@desc …) (@params …) (@return …))` is a function-kind entry, whose parameter and return
    descriptions are paired with the arrow type's argument/return types (or `%Undefined%` when the
    type is absent or not an arrow of the right arity). -/
def getDocOf (env : MinEnv) (w : World) (atom : Atom) : Atom :=
  let atoms := env.atoms ++ w.selfExtra
  let ty := match atom with
    | Atom.sym s => ((env.types.getD s []).head?).getD (Atom.sym "%Undefined%")
    | _ => ((env.exprTypes.find? (fun p => p.1 == atom)).map (·.2)).getD (Atom.sym "%Undefined%")
  match atoms.find? (fun a => match a with
      | Atom.expr (Atom.sym "@doc" :: target :: _) => target == atom
      | _ => false) with
  | some (Atom.expr [_, _, desc, Atom.expr [Atom.sym "@params", Atom.expr params],
                     Atom.expr [Atom.sym "@return", retDesc]]) =>
      let n := params.length
      let (paramTys, retTy) := match ty with
        | Atom.expr (Atom.sym "->" :: rest) =>
            if rest.length == n + 1 then (rest.dropLast, ((rest.getLast?).getD (Atom.sym "%Undefined%")))
            else (List.replicate n (Atom.sym "%Undefined%"), Atom.sym "%Undefined%")
        | _ => (List.replicate n (Atom.sym "%Undefined%"), Atom.sym "%Undefined%")
      let params' := (params.zip paramTys).map (fun pp => match pp.1 with
        | Atom.expr [Atom.sym "@param", pdesc] =>
            Atom.expr [Atom.sym "@param", Atom.expr [Atom.sym "@type", pp.2],
                       Atom.expr [Atom.sym "@desc", pdesc]]
        | other => other)
      Atom.expr [Atom.sym "@doc-formal", Atom.expr [Atom.sym "@item", atom],
        Atom.expr [Atom.sym "@kind", Atom.sym "function"], Atom.expr [Atom.sym "@type", ty], desc,
        Atom.expr [Atom.sym "@params", Atom.expr params'],
        Atom.expr [Atom.sym "@return", Atom.expr [Atom.sym "@type", retTy],
                   Atom.expr [Atom.sym "@desc", retDesc]]]
  | some (Atom.expr [_, _, desc]) =>
      Atom.expr [Atom.sym "@doc-formal", Atom.expr [Atom.sym "@item", atom],
        Atom.expr [Atom.sym "@kind", Atom.sym "atom"], Atom.expr [Atom.sym "@type", ty], desc]
  | _ => Atom.sym "Empty"

mutual

/-- One interpreter step on the top frame (Rust `interpret_stack`). `fuel` bounds the nested
    sub-interpretation performed by `collapse-bind`; `counter` is threaded for gensym (rule-variable
    freshening). A finished item with no parent is a final result. -/
def interpretStack1 (env : MinEnv) (fuel : Nat) (st : St) (it : Item) : List Item × St :=
  match it.stack with
  | [] => ([], st)
  | top :: prev =>
    if top.fin then
      match prev with
      | [] => ([it], st)
      | pf :: pprev =>
        let res := instantiate it.bnd top.atom
        match pf.ret with
        | Ret.chain =>
            match pf.atom with
            | Atom.expr [Atom.sym "chain", _, Atom.var v, templ] =>
                let newFrame : Frame := { pf with atom := Atom.expr [Atom.sym "chain", res, Atom.var v, templ], fin := false }
                ([{ stack := newFrame :: pprev, bnd := it.bnd }], st)
            | _ => ([finItem pprev (errAtom pf.atom "chain: corrupt frame") it.bnd], st)
        | Ret.function =>
            match res with
            | Atom.expr [Atom.sym "return", result] => ([finItem pprev result it.bnd], st)
            | _ =>
                if isEmbeddedOp res then ([{ stack := atomToStack res (pf :: pprev), bnd := it.bnd }], st)
                else
                  let target := match pprev with | g :: _ => g.atom | [] => res
                  ([finItem pprev (errAtom target "NoReturn") it.bnd], st)
        | Ret.none_ => ([], st)
    else
      match top.atom with
      | Atom.expr [Atom.sym "eval", x] => evalOp env st prev x it.bnd
      | Atom.expr [Atom.sym "evalc", x, _space] => evalOp env st prev x it.bnd
      | Atom.expr [Atom.sym "chain", nested, Atom.var v, templ] =>
          ([{ stack := atomToStack (Subst.apply [(v, nested)] templ) prev, bnd := it.bnd }], st)
      | Atom.expr [Atom.sym "unify", a, p, t, e] => (unifyOp prev a p t e it.bnd, st)
      | Atom.expr [Atom.sym "cons-atom", h, Atom.expr t] => ([finItem prev (Atom.expr (h :: t)) it.bnd], st)
      | Atom.expr [Atom.sym "cons-atom", _, _] =>
          ([finItem prev (errAtom top.atom "cons-atom: expected (cons-atom <head> (: <tail> Expression))") it.bnd], st)
      | Atom.expr [Atom.sym "decons-atom", Atom.expr (h :: t)] => ([finItem prev (Atom.expr [h, Atom.expr t]) it.bnd], st)
      | Atom.expr [Atom.sym "decons-atom", _] =>
          ([finItem prev (errAtom top.atom "decons-atom: expected (decons-atom (: <expr> Expression))") it.bnd], st)
      | Atom.expr [Atom.sym "context-space"] => ([finItem prev (Atom.sym "&self") it.bnd], st)
      | Atom.expr [Atom.sym "get-type", x]
      | Atom.expr [Atom.sym "get-type", x, _space]
      | Atom.expr [Atom.sym "get-type-space", _space, x] =>
          -- `(get-type atom)`, plus the space-parameterised `(get-type atom space)` (used by
          -- `type-cast`) and `(get-type-space space atom)`: the space names the type environment, and
          -- `env` carries the program's `(: …)` declarations, the `&self`/context environment these
          -- queries target, so all three type `x` identically.
          --
          -- An ill-typed application has *no* type: `get-type` returns no results when an argument
          -- violates the operator's declared signature (d1_gadt: `(get-type (+ 5 "4"))` is `()`).
          -- Otherwise the inferred type(s), with grounded operations inside the type REDUCED. d3's
          -- dependent `(: ConsN (-> $t (VecN $t $x) (VecN $t (+ $x 1))))` makes
          -- `(ConsN "1" NilN) : (VecN String (+ 0 1))`, which must reduce to `(VecN String 1)`
          -- ("the result returned by get-type is reduced"). Reduction is a no-op on grounded-free
          -- types (symbolic `(Vec Number (S (S Z)))`, atomic `Number`), so b5/d1 are unchanged.
          let xi := instantiate it.bnd x
          let emit : St → List Item × St := fun st0 =>
            (getTypes env (typePrep st.world xi)).foldl (fun (acc : List Item × St) t =>
              let (rs, st2) := mettaEval env fuel acc.2 it.bnd t
              (acc.1 ++ rs.map (fun p => finItem prev p.1 it.bnd), st2)) ([], st0)
          match xi with
          | Atom.expr (Atom.sym op :: args) =>
              if (typeMismatch env st.world op args).isSome then ([], st) else emit st
          | Atom.expr (f :: args) =>
              -- Expression-headed application (head is not a bare symbol, e.g. the partial
              -- application `(curry-a + 2)`): no type if the head's function type rejects an
              -- argument (d2: `(get-type ((curry-a + 2) "S"))` is `()`).
              let illTyped := (getTypes env (typePrep st.world f)).any (fun ft => match ft with
                | Atom.expr (Atom.sym "->" :: ts) =>
                    (typeCheckArgs env st.world ts.dropLast 0 [] args).isSome
                | _ => false)
              if illTyped then ([], st) else emit st
          | _ => emit st
      | Atom.expr [Atom.sym "get-doc", x] =>
          -- documentation lookup (g1_docs): build the `@doc-formal` for the (uninterpreted) atom
          -- from its `(@doc …)` facts and declared type, or `Empty` if undocumented. `help!`
          -- (a grounded op below) formats and returns `()`.
          ([finItem prev (getDocOf env st.world (instantiate it.bnd x)) it.bnd], st)
      | Atom.expr [Atom.sym "metta", atom, _typ, _space] =>
          -- full type-directed evaluation of `atom` (Hyperon's `metta` strategy); the result is used
          -- but the sub-evaluation's internal bindings are dropped (Hyperon `apply_and_retain`,
          -- "retain nothing locally"). World effects are threaded through `st`.
          let (pairs, st') := mettaEval env fuel st it.bnd atom
          (pairs.map (fun p => finItem prev p.1 it.bnd), st')
      | Atom.expr [Atom.sym "capture", atom] =>
          -- `(capture atom)` (Hyperon `core.rs : CaptureOp`, type `(-> Atom Atom)`): fully interpret
          -- `atom` in the current space and return its results. The argument is taken quoted and
          -- `capture` does the interpretation itself with `metta`-style full evaluation, local bindings
          -- not retained, which freezes the current nondeterministic context into the result set.
          let (pairs, st') := mettaEval env fuel st it.bnd atom
          (pairs.map (fun p => finItem prev p.1 it.bnd), st')
      | Atom.expr [Atom.sym "metta-thread", atom, _typ, _space] =>
          -- like `metta`, but RETAINS the query-variable solutions of `atom` still live in the
          -- continuation, threading them to sibling expression elements (Hyperon `interpret_tuple`).
          let (pairs, st') := mettaEval env fuel st it.bnd atom
          (pairs.flatMap (fun p =>
             (Bindings.merge it.bnd (restrictBnd (scopeVars it.bnd prev) p.2)).map (finItem prev p.1)), st')
      | Atom.expr [Atom.sym "match", space, pattern, template] =>
          -- Query `space` for `pattern` (single, or a conjunction `(, p1 … pk)`), returning
          -- `template` per solution (Rust `match`). `&self` is the program space (`env.atoms`); a
          -- `bind!`-bound token/handle selects a named space in the world. Matched atoms are
          -- freshened so their variables cannot capture query variables.
          let rawSpace := match spaceName st.world (instantiate it.bnd space) with
            | some "&self" => env.atoms ++ st.world.selfExtra
            | some name => st.world.spaces.getD name []
            | none => env.atoms ++ st.world.selfExtra
          -- deref state handles in the stored atoms, and substitute tokens + deref states in the
          -- pattern, so `match` compares by state *content* (e3: a pattern `… &state-active` matches a
          -- stored `(= … (State k))` when both cells hold the same value). Both maps are the identity
          -- when there are no states/tokens, so ordinary spaces (e1/c2/&self KB) are unchanged.
          let spaceAtoms := rawSpace.map (resolveStates st.world)
          let patterns := match subTokens st.world pattern with
            | Atom.expr (Atom.sym "," :: ps) => ps.map (resolveStates st.world)
            | p => [resolveStates st.world p]
          let (sols, st') := matchConj spaceAtoms patterns st [it.bnd]
          (sols.filterMap fun m =>
            if Bindings.hasLoop m then none else some (finItem prev (instantiate m template) m), st')
      | Atom.expr [Atom.sym "superpose-bind", Atom.expr pairs] =>
          (pairs.map (superposeItem prev it.bnd), st)
      | Atom.expr [Atom.sym "collapse-bind", nested] =>
          let (atoms, st') := interpretFuel env fuel st [{ stack := atomToStack nested [], bnd := it.bnd }] []
          ([finItem prev (Atom.expr (atoms.map (fun p => Atom.expr [p.1, Atom.unit]))) it.bnd], st')
      -- ── mutable state cells (e2/e3) and named spaces (e1/c2), operating on the threaded `world` ──
      | Atom.expr [Atom.sym "new-state", v] =>
          -- allocate a fresh cell holding `v`; return the handle `(State <id>)`
          let (id, st') := st.fresh
          ([finItem prev (stateHandle id) it.bnd], st'.mapWorld (·.setStore id (instantiate it.bnd v)))
      | Atom.expr [Atom.sym "get-state", s] =>
          match stateId st.world (instantiate it.bnd s) with
          | some id => ([finItem prev (st.world.store.getD id emptyA) it.bnd], st)
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "get-state: not a state") it.bnd], st)
      | Atom.expr [Atom.sym "change-state!", s, v] =>
          match stateId st.world (instantiate it.bnd s) with
          | some id =>
              ([finItem prev (stateHandle id) it.bnd], st.mapWorld (·.setStore id (instantiate it.bnd v)))
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "change-state!: not a state") it.bnd], st)
      | Atom.expr [Atom.sym "new-space"]
      | Atom.expr [Atom.sym "new-mork-space"] =>
          -- Allocate a fresh empty named space; return its handle token. `new-mork-space` is
          -- identical: a MORK space and an ordinary named space share the add/remove/match contract
          -- (MORK is a storage backend, specifically a high-performance trie, not a semantic difference), so its
          -- observable behaviour under add-atom/remove-atom/match is the same as `new-space`.
          let (id, st') := st.fresh
          let name := "&space-" ++ toString id
          ([finItem prev (Atom.sym name) it.bnd], st'.mapWorld (·.newSpace name))
      | Atom.expr [Atom.sym "fork-space", s] =>
          -- `(fork-space S)`: an independent copy of space `S`, a fresh space seeded with a snapshot
          -- of S's current atoms. Atom lists are immutable, so the fork and `S` evolve independently
          -- with no aliasing (c2's parent/child/grandchild spaces). A non-space argument is a type
          -- error, reported as such (matching `add-atom`).
          match spaceName st.world (instantiate it.bnd s) with
          | some src =>
              let srcAtoms := if src == "&self" then env.atoms ++ st.world.selfExtra
                              else st.world.spaces.getD src []
              let (id, st') := st.fresh
              let name := "&space-" ++ toString id
              ([finItem prev (Atom.sym name) it.bnd], st'.mapWorld (fun w => (w.newSpace name).appendSpace name srcAtoms))
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "fork-space: not a space") it.bnd], st)
      | Atom.expr [Atom.sym "add-atom", s, a] =>
          -- `&self` is the program space: added atoms (often `=` rules, as in e3's `new-goal-status!`)
          -- go to `world.selfExtra`, which both `match &self` and rule evaluation (`candidatesW`)
          -- consult; any other token names a separate space in `world.spaces`.
          match spaceName st.world (instantiate it.bnd s) with
          | some "&self" => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.appendSelf [instantiate it.bnd a]))
          | some name => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.appendSpace name [instantiate it.bnd a]))
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "add-atom: not a space") it.bnd], st)
      | Atom.expr [Atom.sym "remove-atom", s, a] =>
          match spaceName st.world (instantiate it.bnd s) with
          | some "&self" => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.eraseSelf (instantiate it.bnd a)))
          | some name => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.eraseFromSpace name (instantiate it.bnd a)))
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "remove-atom: not a space") it.bnd], st)
      | Atom.expr [Atom.sym "get-atoms", s] =>
          match spaceName st.world (instantiate it.bnd s) with
          | some "&self" => ((env.atoms ++ st.world.selfExtra).map (fun x => finItem prev x it.bnd), st)
          | some name => ((st.world.spaces.getD name []).map (fun x => finItem prev x it.bnd), st)
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "get-atoms: not a space") it.bnd], st)
      | Atom.expr [Atom.sym "bind!", tok, val] =>
          -- bind a token to the (already-evaluated) value; resolved by `resolveTok` when used
          match instantiate it.bnd tok with
          | Atom.sym t => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.bindTok t (instantiate it.bnd val)))
          | other => ([finItem prev (errAtom other "bind!: token must be a symbol") it.bnd], st)
      | Atom.expr [Atom.sym "import!", space, file] =>
          -- load a module's atoms (pre-read into `env.imports` by the IO runner) into a space:
          -- `&self` extends the current program space (visible to later queries only); any other
          -- token names a separate space (`&kb`), created/extended in the world. Returns `()`.
          let fileAtoms := match instantiate it.bnd file with
            | Atom.sym f => env.imports.getD f []
            | _ => []
          match spaceName st.world (instantiate it.bnd space) with
          | some "&self" => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.appendSelf fileAtoms))
          | some name => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.appendSpace name fileAtoms))
          | none => ([finItem prev (errAtom (instantiate it.bnd space) "import!: target is not a space") it.bnd], st)
      | _ =>
          if isEmbeddedOp top.atom then
            ([finItem prev (errAtom top.atom "unsupported minimal op") it.bnd], st)
          else
            ([{ stack := { top with fin := true } :: prev, bnd := it.bnd }], st)
  termination_by 3 * fuel + 2
  decreasing_by all_goals (simp_wf <;> omega)

/-- Fuel-bounded interpretation driver (Rust `interpret`'s loop). Processes the work queue,
    collecting finished results and threading the gensym `counter`, until the queue empties or
    fuel runs out. -/
def interpretFuel (env : MinEnv) (fuel : Nat) (st : St) (work : List Item) (done : List (Atom × Bindings)) : List (Atom × Bindings) × St :=
  -- `done` accumulates results (with their bindings) in reverse so each step is O(1); reversed once
  -- on exit. Bindings are kept so callers can propagate query-variable solutions; `st` threads the
  -- gensym counter and the mutable world.
  match fuel, work with
  | _, [] => (done.reverse, st)
  | 0, w => (done.reverse ++ w.map (fun it => if isFinal it then finalPair it else exhaustedPair it), st)
  | f + 1, it :: rest =>
      let (results, st') := interpretStack1 env f st it
      let finals := (results.filter isFinal).map finalPair
      let more := results.filter (fun r => !isFinal r)
      interpretFuel env f st' (more ++ rest) (finals.reverse ++ done)
  termination_by 3 * fuel
  decreasing_by all_goals (simp_wf <;> omega)

/-- Full MeTTa evaluation (`metta`): evaluate each argument whose declared type is not `Atom`, then
    reduce the resulting application to a fixpoint, treating `NotReducible` as "keep the atom".
    Nondeterministic and fuel-bounded. This is the metta-call loop with type-directed argument
    evaluation on top of the minimal interpreter, and is mutual with the interpreter so that the
    `metta` instruction itself uses it. -/
def mettaEval (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (a : Atom) : List (Atom × Bindings) × St :=
  match fuel with
  | 0 =>
      -- Fuel exhausted: signal it explicitly as MeTTa's `StackOverflow` error (language spec:
      -- "returned by the interpreter when the stack depth is restricted and maximum depth is
      -- reached") rather than returning the unevaluated atom as if it were a normal form, so an
      -- exhausted evaluation is distinguishable from a genuine result (replayability/auditing).
      ([(Atom.expr [Atom.sym "Error", instantiate bnd a, Atom.sym "StackOverflow"], bnd)], st)
  | fuel + 1 =>
    match instantiate bnd a with
    | Atom.expr (Atom.sym op :: args) =>
      if let some (pos, expected, actual) := typeMismatch env st.world op args then
        -- runtime type error: a declared parameter type rejects an argument (Hyperon `BadArgType`)
        ([(Atom.expr [Atom.sym "Error", Atom.expr (Atom.sym op :: args),
            Atom.expr [Atom.sym "BadArgType", Atom.gnd (Ground.int (Int.ofNat pos)), expected, actual]], bnd)], st)
      else
        -- (1) type-directed argument evaluation, THREADING query-variable bindings across arguments
        --     (Hyperon `apply_and_retain`): a solution found while evaluating one argument (e.g.
        --     `$x = Fritz` from the `Bool` cond `(green $x)`) is retained, restricted to the
        --     expression's own query variables so introduced/`let`-local variables don't leak, and
        --     reaches its siblings (so `(ift (green $x) $x)` returns `Fritz`). The argument list is
        --     nondeterministic, so this is a binding-threaded cartesian product; `st` (gensym + world)
        --     threads through it so mutations sequence left-to-right.
        let queryVars := args.flatMap Atom.vars
        let (partials, st1) := (args.zip (argMask env op args.length)).foldl
          (fun (acc : List (List Atom × Bindings) × St) ae =>
            acc.1.foldl (fun (acc2 : List (List Atom × Bindings) × St) part =>
              if ae.2 then
                let (ps, st') := mettaEval env fuel acc2.2 part.2 ae.1
                (acc2.1 ++ ps.map (fun p =>
                  (part.1 ++ [p.1], restrictBnd queryVars ((Bindings.merge part.2 p.2).head?.getD p.2))), st')
              else
                (acc2.1 ++ [(part.1 ++ [instantiate part.2 ae.1], part.2)], acc2.2)) ([], acc.2))
          ([([], [])], st)
        -- (2) reduce each (binding-threaded) combination; leave inert on Atom-return (`metta_call`)
        --     or re-evaluate, carrying the threaded query bindings forward
        partials.foldl
          (fun (acc : List (Atom × Bindings) × St) part =>
            -- Error propagation (Hyperon `interpret_args`): if a type-directed-evaluated argument
            -- *reduced to* an `(Error …)`, the whole application becomes that error, so
            -- `(f (+ 5 "S"))` ↦ `(Error (+ 5 "S") (BadArgType 2 Number String))`. The `h ≠ orig`
            -- guard is the spec's `$h != $atom`: an `Atom`-typed argument passed through unevaluated
            -- (or a literal error datum) is unchanged, so `assert*` still receives and *compares*
            -- error results rather than propagating them.
            match (part.1.zip args).find? (fun ho => ho.1.isError && ho.1 != ho.2) with
            | some (err, _) => (acc.1 ++ [(err, part.2)], acc.2)
            | none =>
            let w := Atom.expr (Atom.sym op :: part.1)
            let (pairs, st') := interpretFuel env (fuel + 1) acc.2
              [{ stack := atomToStack (Atom.expr [Atom.sym "eval", w]) [], bnd := bnd }] []
            let (out, st'') := pairs.foldl (fun (a2 : List (Atom × Bindings) × St) p =>
              let pb := restrictBnd queryVars ((Bindings.merge part.2 p.2).head?.getD p.2)
              if p.1 == notReducibleA || p.1 == w then (a2.1 ++ [(w, part.2)], a2.2)
              else if returnsAtom env w && !isEmbeddedOp p.1 then (a2.1 ++ [(p.1, pb)], a2.2)
              else let (more, st3) := mettaEval env fuel a2.2 pb p.1
                   -- re-merge the threaded query bindings `pb`: re-evaluating `p.1` produces fresh
                   -- output bindings that need not mention a query variable bound *inside* the
                   -- evaluated argument (e.g. `$goal`, when the argument reduced to a state handle
                   -- `(State k)` that no longer contains `$goal`). Without this, that solution is lost
                   -- to the continuation, so `(get-state (status (Goal $goal)))` would drop `$goal`.
                   (a2.1 ++ more.map (fun m =>
                      (m.1, restrictBnd queryVars ((Bindings.merge pb m.2).head?.getD m.2))), st3)) ([], st')
            (acc.1 ++ out, st'')) ([], st1)
    | Atom.expr (e :: rest) =>
        -- Expression-headed application. FIRST try to reduce the whole expression by an equality
        -- rule: higher-order combinators are defined with expression-headed left-hand sides, e.g.
        -- `(= (((curry $f) $x) $y) ($f $x $y))`, so `(((curry +) 2) 3)` must match that rule and
        -- reduce to `(+ 2 3)` (Hyperon's `interpret_expression` tries function application before
        -- tuple). If no rule fires (data tuples like `(1 2 3)`, partial applications like
        -- `((curry +) 2)`), fall back to element-wise tuple interpretation (`interpret_tuple`),
        -- which keeps a binding made in one element live for its siblings.
        let whole := Atom.expr (e :: rest)
        let (ruleRes, st1) := interpretFuel env (fuel + 1) st
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", whole]) [], bnd := bnd }] []
        let reduced := ruleRes.filter (fun p => p.1 != whole && p.1 != notReducibleA)
        if reduced.isEmpty then
          let (tupleRes, st2) := interpretFuel env (fuel + 1) st1
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr [Atom.sym "interpret-tuple", whole, Atom.sym "&self"]]) [], bnd := bnd }] []
          -- Re-evaluate a tuple result whose head reduced into a *new* application, e.g.
          -- `((is-socrates) Human)` → `((curry-a is Socrates) Human)` → `(is Socrates Human)` → `True`.
          -- A result identical to the input is a normal-form tuple, kept as-is (no re-eval, no loop).
          tupleRes.foldl (fun (acc : List (Atom × Bindings) × St) p =>
            if p.1 == whole then (acc.1 ++ [p], acc.2)
            else let (more, st') := mettaEval env fuel acc.2 p.2 p.1; (acc.1 ++ more, st')) ([], st2)
        else
          reduced.foldl (fun (acc : List (Atom × Bindings) × St) p =>
            let (more, st') := mettaEval env fuel acc.2 p.2 p.1
            (acc.1 ++ more, st')) ([], st1)
    | w =>
        -- a bare symbol/variable/grounded atom: reduce once, then re-evaluate or leave inert
        let (pairs, st') := interpretFuel env (fuel + 1) st
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", w]) [], bnd := bnd }] []
        pairs.foldl (fun (a2 : List (Atom × Bindings) × St) p =>
          if p.1 == notReducibleA || p.1 == w then (a2.1 ++ [(w, bnd)], a2.2)
          else if returnsAtom env w && !isEmbeddedOp p.1 then (a2.1 ++ [p], a2.2)
          else let (more, st3) := mettaEval env fuel a2.2 p.2 p.1; (a2.1 ++ more, st3)) ([], st')
  termination_by 3 * fuel + 1
  decreasing_by all_goals (simp_wf <;> omega)

end

/-- Interpret `atom` directly under `kb`/`gt` with `fuel` steps (no implicit `eval`). -/
def interpretAtom (env : MinEnv) (fuel : Nat) (atom : Atom) : List Atom :=
  (interpretFuel env fuel St.init [{ stack := atomToStack atom [] }] []).1.map (·.1)

/-- Evaluate `atom` (i.e. interpret `(eval atom)`) under `kb`/`gt` with `fuel` steps. -/
def evalAtomMin (env : MinEnv) (fuel : Nat) (atom : Atom) : List Atom :=
  interpretAtom env fuel (Atom.expr [Atom.sym "eval", atom])

end Metta.Minimal
