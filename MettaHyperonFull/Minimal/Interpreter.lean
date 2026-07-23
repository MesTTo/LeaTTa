-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Minimal.Interpreter
Layer: Minimal
Purpose: A Lean port of Hyperon's minimal MeTTa interpreter (`interpreter.rs`), a
  continuation-passing nondeterministic stack machine over the minimal instruction set
  (`eval`, `evalc`, `chain`, `unify`, `cons-atom`, `decons-atom`, `function`/`return`,
  `collapse-bind`, `superpose-bind`, `metta`, `metta-thread`, `capture`, `context-space`) plus the
  embedded space, state, and type operations (`match`, `get-type`, `add-atom`, `bind!`, `import!`).
  The stack is an immutable list of frames (head is the top) and the return handler is an explicit
  tag. One step (`interpretStack1`) is total; the driver (`interpretFuel`) is fuel-bounded because
  MeTTa programs may fail to terminate. The type-directed evaluator (`mettaEval`) sits on top.
Imports: MettaHyperonFull.Core (Matching, Space, Builtins), Std.Data.HashMap
Trusted boundary: none
Main exports: Frame, Stack, Item, MinEnv, World, St, atomToStack, queryOp, evalOp, getTypes,
  matchType, typeMismatch, interpretStack1, interpretFuel, mettaEval, interpretAtom, evalAtomMin
Open obligations: fuel is shared with the nested `collapse-bind` driver, so deeply nested calls
  deplete the outer budget; on exhaustion, unfinished items surface as `StackOverflow` rather than
  resumable partial results.
-/
import MettaHyperonFull.Minimal.CaptureAvoidingFreshening
import MettaHyperonFull.Core.Space
import MettaHyperonFull.Core.Builtins
import Std.Data.HashMap

namespace Metta.Minimal
open Metta

/-- Return-handler tag, replacing the Rust `ReturnHandler` fn-pointer. -/
inductive Ret where
  | none_
  | chain
  | function
  deriving Repr, BEq, Inhabited

/-- One stack frame: the atom being interpreted (or, when `fin`, the value being returned),
    its return handler, its variable scope, and a flag marking it finished. -/
structure Frame where
  /-- The atom being interpreted, or the return value when `fin = true`. -/
  atom : Atom
  /-- Return handler: decides how this frame's result is delivered to the parent. -/
  ret : Ret := Ret.none_
  /-- Variable scope: rule-variables retained for cross-argument binding propagation. -/
  vars : List VarName := []
  /-- `true` once `atom` holds a finished value rather than pending work. -/
  fin : Bool := false
  deriving Inhabited

/-- Evaluation stack: head is the top (current) frame; tail is the parent chain. -/
abbrev Stack := List Frame

/-- Every live variable spelling retained by a continuation, including explicit frame scopes and
variables occurring in the frame atoms themselves. -/
def liveStackVars (stack : Stack) : List VarName :=
  stack.flatMap fun frame => frame.vars ++ frame.atom.vars

/-- One work item in the nondeterministic queue: a stack plus the bindings accumulated so far. -/
structure Item where
  /-- The evaluation stack for this branch. -/
  stack : Stack
  /-- Variable bindings accumulated on this branch. -/
  bnd : Bindings := []
  deriving Inhabited

/-- `NotReducible`: returned when no equality rule applies to an atom. -/
def notReducibleA : Atom := Atom.sym "NotReducible"
/-- `Empty`: returned to drop a nondeterministic branch. -/
def emptyA : Atom := Atom.sym "Empty"

/-- Build `(Error <atom> <message>)` with the message as a symbol (matching the interpreter ops). -/
def errAtom (a : Atom) (msg : String) : Atom := Atom.expr [Atom.sym "Error", a, Atom.sym msg]

/-- Runtime message for malformed primitive `unify` applications. -/
def unifyBadArityMessage : Atom → String
  | Atom.expr [Atom.sym "unify", Atom.sym a, Atom.sym p, Atom.sym t] =>
      "expected: (unify <atom> <pattern> <then> <else>), found: " ++
        "(unify " ++ a ++ " " ++ p ++ " " ++ t ++ ")"
  | source =>
      "expected: (unify <atom> <pattern> <then> <else>), found: " ++
        toString source

/-- Copy the variable scope from the top frame of `prev` (Rust `Stack::vars_copy`). -/
def varsCopy : Stack → List VarName
  | [] => []
  | f :: _ => f.vars

/-- Variables retained by a `chain` frame: the enclosing frame scope plus
variables shared by the nested computation and the continuation template.
This is the ordered-list realization of Hyperon's `chain_to_stack`
intersection. -/
def chainFrameVars (prev : Stack) (nested template : Atom) : List VarName :=
  (varsCopy prev ++ nested.vars.filter fun name =>
    template.vars.contains name).eraseDups

/-- Return `true` if the atom is an embedded minimal-MeTTa operation. -/
def isEmbeddedOp : Atom → Bool
  | Atom.expr (Atom.sym op :: _) =>
      ["eval", "evalc", "chain", "unify", "cons-atom", "decons-atom", "function",
       "collapse-bind", "superpose-bind", "metta", "metta-thread", "capture", "context-space", "match",
       "get-type", "get-type-space", "get-doc", "new-state", "get-state", "change-state!", "new-space",
       "new-mork-space", "fork-space", "add-atom", "remove-atom",
       "get-atoms", "bind!", "import!"].contains op
  | _ => false

/-- Push `atom` onto `prev`, expanding `chain`/`function`/`unify` into their frame shapes and
    descending into the nested sub-atom (Rust `atom_to_stack`). Structural on `atom`, so total. -/
def atomToStack : Atom → Stack → Stack
  | a, prev =>
    match a with
    | Atom.expr [Atom.sym "chain", nested, Atom.var v, templ] =>
        atomToStack nested ({ atom := Atom.expr [Atom.sym "chain", nested, Atom.var v, templ],
                              ret := Ret.chain,
                              vars := chainFrameVars prev nested templ } :: prev)
    | Atom.expr [Atom.sym "function", Atom.expr body] =>
        atomToStack (Atom.expr body) ({ atom := Atom.expr [Atom.sym "function", Atom.expr body],
                                        ret := Ret.function, vars := varsCopy prev } :: prev)
    | Atom.expr [Atom.sym "unify", ua, up, ut, ue] =>
        { atom := Atom.expr [Atom.sym "unify", ua, up, ut, ue], ret := Ret.none_ } :: prev
    | Atom.expr (Atom.sym "chain" :: _) =>
        { atom := errAtom a "chain: expected (chain <nested> $var <templ>)", fin := true } :: prev
    | Atom.expr (Atom.sym "function" :: _) =>
        { atom := errAtom a "function: expected (function <expression>)", fin := true } :: prev
    | Atom.expr (Atom.sym "unify" :: _) =>
        { atom := errAtom a (unifyBadArityMessage a), fin := true } :: prev
    | _ => { atom := a, vars := varsCopy prev } :: prev

/-- Make a finished item: a single frame carrying `a` on top of `st`. -/
def finItem (st : Stack) (a : Atom) (b : Bindings) : Item := { stack := { atom := a, fin := true } :: st, bnd := b }

/-- Wrap one eval result (Rust `eval_result`): a `(function ...)` result opens a new
    function scope; any other result is finished immediately. -/
def evalResult (prev : Stack) (r : Atom) (b : Bindings) : Item :=
  match r with
  | Atom.expr (Atom.sym "function" :: _) => { stack := atomToStack r prev, bnd := b }
  | _ => finItem prev r b

/-- Return `true` for a variable or an expression whose head is (recursively) a variable.
    Such atoms are not reduced by the interpreter (Rust `is_variable_op`); without this guard
    a bare variable would match the left-hand side of every equality rule. -/
def isVariableHeaded : Atom → Bool
  | Atom.var _ => true
  | Atom.expr (h :: _) => isVariableHeaded h
  | _ => false

/-- Dispatch key of an atom: its head symbol (for an expression) or itself (for a symbol).
    Only rules with the same key can match a given query. This is first-argument indexing,
    the same approach PeTTa borrows from Prolog's clause indexing. -/
def headKey : Atom → Option String
  | Atom.sym s => some s
  | Atom.expr (Atom.sym h :: _) => some h
  | _ => none

open Std in
/-- Precomputed evaluation environment. Built once per knowledge base so the hot path
    never rescans the whole atom list. -/
structure MinEnv where
  /-- `=`-rules indexed by the head key of their LHS (first-argument rule indexing). -/
  ruleIndex : HashMap String (List (Atom × Atom))
  /-- `=`-rules whose LHS has no head key (variable- or non-symbol-headed); candidates for every query. -/
  varRules : List (Atom × Atom)
  /-- Grounding table: implementations of the built-in operations. -/
  gt : GroundingTable
  /-- Identity of the space in which this environment evaluates.  The public
      `context-space` instruction exposes it as an opaque `SpaceType` grounding,
      never as an ordinary symbol. -/
  contextName : String
  /-- Full atom list of the space (used by `match`, which queries all atoms, not just `=` rules). -/
  atoms : List Atom
  /-- User-visible atoms in `&self`, excluding prelude/runtime support rules. Observable space
      operations such as `match &self`, `get-atoms &self`, and `fork-space &self` use this list. -/
  visibleAtoms : List Atom
  /-- Declared types of each symbol from `(: sym T)` atoms (arrow or not), for `get-type` and
      runtime type-checking. A symbol may have several declared types (e.g. `(: Ten Nat)` and
      `(: Ten Int)`), matching Hyperon's `get_atom_types : ... -> Vec<AtomType>`. -/
  types : HashMap String (List Atom)
  /-- Pre-read `import!` targets: each module name mapped to the atoms from its file.
      The file read is IO and happens once in the runner (`Main`); the `import!` instruction
      itself is pure and looks the atoms up here. -/
  imports : HashMap String (List Atom)
  /-- Immediate module dependencies discovered while pre-reading imports. Runtime `import! &self`
      follows these dependencies before exposing the importing module's exported atoms. -/
  importDeps : HashMap String (List String)
  /-- Declared types of expression subjects, from `(: (e ...) T)` atoms (e.g. `(: (A B) PairAB)`),
      kept separate from `types` (keyed by symbol). A direct declaration takes precedence over
      the type inferred for an application in `getTypes`. -/
  exprTypes : List (Atom × Atom)

/-- Extract the `(= lhs rhs)` equality rules from an atom list. Factored out so
    `Proofs/IndexingComplete.lean` can characterise the index against this definition. -/
def extractRules (atoms : List Atom) : List (Atom × Atom) :=
  atoms.filterMap fun x => match x with
    | Atom.expr [Atom.sym "=", lhs, rhs] => some (lhs, rhs)
    | _ => none

open Std in
/-- Build a `MinEnv` from a flat atom list and a grounding table. Indexes `(= lhs rhs)` atoms by
    `headKey lhs`, preserving knowledge-base order within each bucket, and collects every
    `(: subject type)` declaration in source order.  Evaluation consults this one ordered type
    index directly; there is no second, last-write-wins signature cache. -/
def MinEnv.ofAtomsGT (atoms : List Atom) (gt : GroundingTable) : MinEnv :=
  let rules : List (Atom × Atom) := extractRules atoms
  -- Index `=`-rules by head key in one pass (`alter`, appending each rule in knowledge-base
  -- order); head-less rules form `varRules` below. This single pass preserves KB order, so
  -- `ruleIndex.getD k` and `varRules` have clean equational characterisations (`Proofs/IndexingComplete`).
  let idx := rules.foldl
    (fun (m : HashMap String (List (Atom × Atom))) lr =>
      match headKey lr.fst with
      | some k => m.alter k (fun cur => some ((cur.getD []) ++ [lr]))
      | none => m)
    HashMap.emptyWithCapacity
  let types := atoms.foldl (fun (m : HashMap String (List Atom)) x => match x with
    | Atom.expr [Atom.sym ":", Atom.sym s, t] => m.insert s (m.getD s [] ++ [t])
    | _ => m) HashMap.emptyWithCapacity
  let exprTypes := atoms.filterMap fun x => match x with
    | Atom.expr [Atom.sym ":", Atom.expr es, t] => some (Atom.expr es, t)
    | _ => none
  { ruleIndex := idx, varRules := rules.filter (fun lr => (headKey lr.fst).isNone),
    gt := gt, contextName := "&self", atoms := atoms, visibleAtoms := atoms, types := types,
    imports := HashMap.emptyWithCapacity, importDeps := HashMap.emptyWithCapacity, exprTypes := exprTypes }

/-- Candidate `=`-rules for `toEval`: rules keyed by its head symbol plus all non-symbol-headed rules. -/
def MinEnv.candidates (env : MinEnv) (toEval : Atom) : List (Atom × Atom) :=
  (match headKey toEval with | some k => env.ruleIndex.getD k [] | none => []) ++ env.varRules

open Std in
/-- Mutable evaluation world: named spaces, state cells, and `bind!`-bound tokens. Threaded
    state-in/state-out through the nondeterministic folds so each mutation is visible to later
    steps and later top-level queries. This is the pure analogue of Hyperon's `Rc<RefCell>` spaces. -/
structure World where
  /-- Named spaces (`new-space`/`add-atom`/`remove-atom`/`match`), keyed by handle name. -/
  spaces : HashMap String (List Atom)
  /-- State cells (`new-state`/`get-state`/`change-state!`), keyed by cell id. -/
  store : HashMap Nat Atom
  /-- `bind!`-bound tokens, mapping each token symbol to its value (e.g. a space handle). -/
  tokens : HashMap String Atom
  /-- Atoms imported into `&self` via `import!`, kept separate from `MinEnv.atoms`.
      `evalSequential` rebuilds the KB each step; threading here means an `import! &self`
      is visible only to the queries that follow it, matching Hyperon's order-sensitive processing. -/
  selfExtra : List Atom
  /-- Module atoms imported into `&self`. These participate in evaluation but are hidden from
      observable space contents such as `get-atoms &self`, matching Hyperon's module isolation. -/
  selfImports : List Atom
  /-- Imported `(target,module)` keys. Re-importing the same module into the same target is a no-op. -/
  imported : List String

open Std in
/-- Empty world: no named spaces, state cells, tokens, or `&self` atoms. -/
def World.empty : World :=
  { spaces := HashMap.emptyWithCapacity, store := HashMap.emptyWithCapacity,
    tokens := HashMap.emptyWithCapacity, selfExtra := [], selfImports := [], imported := [] }

def World.setStore (w : World) (id : Nat) (v : Atom) : World := { w with store := w.store.insert id v }
def World.newSpace (w : World) (name : String) : World := { w with spaces := w.spaces.insert name [] }
/-- Append `atoms` to named space `name`, creating it if absent. -/
def World.appendSpace (w : World) (name : String) (atoms : List Atom) : World :=
  { w with spaces := w.spaces.alter name fun cur => some ((cur.getD []) ++ atoms) }
/-- Remove the first occurrence of `a` from named space `name`. -/
def World.eraseFromSpace (w : World) (name : String) (a : Atom) : World :=
  { w with spaces := w.spaces.alter name fun cur => some ((cur.getD []).erase a) }
/-- Append atoms to the `&self` extension (`add-atom`/`import! &self`). -/
def World.appendSelf (w : World) (atoms : List Atom) : World := { w with selfExtra := w.selfExtra ++ atoms }
/-- Append hidden module atoms to `&self` for evaluation without exposing them through `get-atoms`. -/
def World.appendSelfImport (w : World) (atoms : List Atom) : World :=
  { w with selfImports := w.selfImports ++ atoms }
/-- Remove the first occurrence of `a` from the `&self` extension. -/
def World.eraseSelf (w : World) (a : Atom) : World := { w with selfExtra := w.selfExtra.erase a }
def World.bindTok (w : World) (t : String) (v : Atom) : World := { w with tokens := w.tokens.insert t v }

def World.importKey (target moduleName : String) : String := target ++ "::" ++ moduleName
def World.hasImport (w : World) (target moduleName : String) : Bool :=
  w.imported.contains (World.importKey target moduleName)
def World.markImport (w : World) (target moduleName : String) : World :=
  { w with imported := World.importKey target moduleName :: w.imported }

/-- Threaded interpreter state: the gensym `counter` and the mutable `world`. Replaces the bare
    `Nat` counter that used to thread through the interpreter, so space/state effects ride alongside
    rule-variable freshening. -/
structure St where
  /-- Gensym counter: source of fresh rule-variable suffixes and state-cell/space ids. -/
  counter : Nat
  /-- Mutable world (named spaces, state cells, tokens) threaded through evaluation. -/
  world : World

def St.init : St := { counter := 0, world := World.empty }

def St.fresh (st : St) : Nat × St := (st.counter, { st with counter := st.counter + 1 })

def St.mapWorld (st : St) (f : World → World) : St := { st with world := f st.world }

/-- Resolve a `bind!`-bound token (e.g. `&kb`, `&state-token`) to its value. Other atoms pass through unchanged. -/
def resolveTok (w : World) (a : Atom) : Atom :=
  match a with
  | Atom.sym s => (w.tokens[s]?).getD a
  | _ => a

/-- Build a state-cell handle `(State <id>)`. -/
def stateHandle (id : Nat) : Atom := Atom.expr [Atom.sym "State", Atom.gnd (Ground.int (Int.ofNat id))]

/-- Extract the cell id from a state handle after token resolution, or `none` if not a handle. -/
def stateId (w : World) (a : Atom) : Option Nat :=
  match resolveTok w a with
  | Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)] => some id.toNat
  | _ => none

/-- Opaque grounded representation of a runtime space handle.  `SpaceType` is
the declared public type of `context-space`; the payload is private host data. -/
def contextSpaceAtom (name : String) : Atom :=
  Atom.gnd (Ground.external "SpaceType" name)

/-- Resolve a space handle or token to its name string (`&self` or a named space).
Symbols remain accepted for source-level compatibility, while evaluator-produced
handles use the opaque grounded representation. -/
def spaceName (w : World) (a : Atom) : Option String :=
  match resolveTok w a with
  | Atom.sym s => some s
  | Atom.gnd (Ground.external "SpaceType" name) => some name
  | _ => none

/-- Replace each `(State id)` handle with the cell's current contents (one hop). Cell contents are
    stored already-resolved, so a single deref is faithful. Two distinct cells holding equal values
    therefore compare equal and match each other, matching Hyperon's `State PartialEq`, which derefs
    the `Rc<RefCell>` and compares the wrapped atom rather than cell identity.
    Structural on the atom, so total. -/
def resolveStates (w : World) : Atom → Atom
  | Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)] =>
      match w.store[id.toNat]? with
      | some v => v
      | none => Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)]
  | Atom.expr xs => Atom.expr (xs.map (resolveStates w))
  | a => a

/-- Substitute every `bind!`-bound token with its value throughout an atom. Hyperon replaces tokens
    at parse time; this replicates that so a token stands for its value wherever it appears
    (e.g. `&state-active` inside a `match` pattern). Structural, so total. -/
def subTokens (w : World) : Atom → Atom
  | Atom.sym s => (w.tokens[s]?).getD (Atom.sym s)
  | Atom.expr xs => Atom.expr (xs.map (subTokens w))
  | a => a

/-- Rewrite each `(State id)` to `(StateValue <contents>)`, carrying the cell value as a sub-term.
    This lets the structural `getTypes` type it as `(StateMonad <type of contents>)` without
    threading the world. Structural, so total. -/
def wrapStates (w : World) : Atom → Atom
  | Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)] =>
      match w.store[id.toNat]? with
      | some v => Atom.expr [Atom.sym "StateValue", v]
      | none => Atom.expr [Atom.sym "State", Atom.gnd (Ground.int id)]
  | Atom.expr xs => Atom.expr (xs.map (wrapStates w))
  | a => a

/-- Prepare an atom for `getTypes`: substitute tokens, then wrap state handles with their contents.
    After this the atom carries no world reference, so `getTypes` is a plain structural function. -/
def typePrep (w : World) (a : Atom) : Atom := wrapStates w (subTokens w a)

/-- Build a type-query environment for a specific space. Hyperon `get-type-space` reads
    declarations from the requested space while the runtime builtins remain available. -/
def typeEnvForSpace (env : MinEnv) (w : World) (space : Atom) : MinEnv :=
  let selected := spaceName w space
  let spaceAtoms := match selected with
    | some "&self" => w.selfExtra ++ w.selfImports
    | some name => w.spaces.getD name []
    | none => []
  { MinEnv.ofAtomsGT (env.atoms ++ spaceAtoms) env.gt with
    contextName := selected.getD env.contextName, visibleAtoms := env.visibleAtoms,
    imports := env.imports, importDeps := env.importDeps }

/-- Build an evaluation environment for `evalc`. Hyperon evaluates against the supplied space while
    keeping grounded operations available from the runner. -/
def evalEnvForSpace (env : MinEnv) (w : World) (space : Atom) : Option MinEnv :=
  match spaceName w space with
  | none => none
  | some "&self" => some { env with contextName := "&self" }
  | some name =>
      let atoms := w.spaces.getD name []
      some { MinEnv.ofAtomsGT atoms env.gt with
        contextName := name, visibleAtoms := atoms, imports := env.imports,
        importDeps := env.importDeps }

/-- Candidate `=`-rules for evaluating `toEval`, including rules added to `&self` at runtime
    (`add-atom &self (= ...)` / `import! &self`). These live in `world.selfExtra` rather than
    the precompiled `MinEnv.ruleIndex`. Runtime rules come after the static ones (knowledge-base
    order) and are filtered by head the same way. -/
def candidatesW (env : MinEnv) (w : World) (toEval : Atom) : List (Atom × Atom) :=
  let extra := (w.selfExtra ++ w.selfImports).filterMap fun x => match x with
    | Atom.expr [Atom.sym "=", lhs, rhs] =>
        match headKey lhs, headKey toEval with
        | some k1, some k2 => if k1 == k2 then some (lhs, rhs) else none
        | none, _ => some (lhs, rhs)
        | _, _ => none
    | _ => none
  env.candidates toEval ++ extra

/-- Freshen each atom returned by `get-atoms`, avoiding the caller's live variables and advancing
the gensym counter for stable hygiene. -/
def freshenSpaceAtoms (st : St) (avoid : List VarName) (atoms : List Atom) : List Atom × St :=
  let (rev, st') := atoms.foldl (fun (acc : List Atom × St) a =>
    let (renamed, nextCounter) := freshenRuleAvoiding acc.2.counter avoid a a
    (renamed.1 :: acc.1, { acc.2 with counter := nextCounter })) ([], st)
  (rev.reverse, st')

/-- Import a module into `&self`, following dependencies first and hiding imported atoms from
    observable `&self` contents. Fuel bounds cycles that are not caught by `World.imported`. -/
def importSelfFuel (env : MinEnv) : Nat → String → World → World
  | 0, _, w => w
  | fuel + 1, moduleName, w =>
      if w.hasImport "&self" moduleName then w
      else
        let wMarked := w.markImport "&self" moduleName
        let wDeps := (env.importDeps.getD moduleName []).foldl
          (fun acc dep => importSelfFuel env fuel dep acc) wMarked
        wDeps.appendSelfImport (env.imports.getD moduleName [])

/-- The variable spellings visible at a query step and therefore forbidden to rule freshening. -/
def queryOpAvoid (prev : Stack) (toEval : Atom) (b : Bindings) : List VarName :=
  b.vars ++ toEval.vars ++ liveStackVars prev

/-- Work items contributed by one query candidate at the current freshening counter. -/
def queryOpItemsOfRule (prev : Stack) (toEval : Atom)
    (b : Bindings) (counter : Nat) (p : Atom × Atom) : List Item :=
  let (lhs', rhs') := (freshenRuleAvoiding counter (queryOpAvoid prev toEval b) p.1 p.2).1
  (matchAtoms lhs' toEval).flatMap fun mb =>
    (Bindings.merge b mb).filterMap fun m =>
      if Bindings.hasLoop m then none
      else some (evalResult prev (instantiate m rhs') m)

/-- One capture-avoiding candidate step of the executable query fold. -/
def queryOpFoldStep (prev : Stack) (toEval : Atom) (b : Bindings) :
    (List Item × St) → (Atom × Atom) → (List Item × St)
  | acc, p =>
      let items := queryOpItemsOfRule prev toEval b acc.2.counter p
      let nextCounter :=
        (freshenRuleAvoiding acc.2.counter (queryOpAvoid prev toEval b) p.1 p.2).2
      (acc.1 ++ items, { acc.2 with counter := nextCounter })

/-- Query the KB for `(= to_eval $X)` and return each matching RHS with merged bindings
    (Rust `query`), threading the gensym counter. Returns `[NotReducible]` when nothing matches.
    Variable-headed atoms are refused without querying. -/
def queryOp (env : MinEnv) (st : St) (prev : Stack) (toEval : Atom) (b : Bindings) : List Item × St :=
  if isVariableHeaded toEval then ([finItem prev notReducibleA b], st) else
  let (results, st') := (candidatesW env st.world toEval).foldl
    (queryOpFoldStep prev toEval b) ([], st)
  if results.isEmpty then ([finItem prev notReducibleA b], st') else (results, st')

/-- `(eval <atom>)` (Rust `eval`/`eval_impl`): apply bindings, then execute a grounded operator,
    push a nested embedded op, or query the space for an equality rule. Threads the gensym counter. -/
def evalOp (env : MinEnv) (st : St) (prev : Stack) (x : Atom) (b : Bindings) : List Item × St :=
  let x' := instantiate b x
  match x' with
  | Atom.expr (Atom.sym op :: args) =>
      -- Grounded ops (`==`, the `assert*` family, arithmetic, ...) compare values, so each argument
      -- has its `bind!` tokens substituted and its state handles dereferenced to cell contents first.
      -- This is what makes `(== (new-state 1) (new-state 1))`, `assertEqual` on states, and
      -- comparisons through a state token compare by content. Embedded ops that need the raw handle
      -- (`get-state`, `change-state!`) take the `noReduce` path below with `x'` (tokens/handles
      -- intact), so they are unaffected.
      match callGrounded env.gt op (args.map (fun a => resolveStates st.world (subTokens st.world a))) with
      | ReduceResult.ok results =>
          -- An empty result set is no results (a dead branch), not the `Empty` atom.
          -- `(superpose ())` contributes nothing; `(if False _ (superpose ()))` drops its branch (e3).
          -- Ops that want to yield `Empty` do so explicitly (`ok [Empty]`).
          (results.map (fun r => evalResult prev r b), st)
      | ReduceResult.runtimeError msg => ([finItem prev (errAtom x' msg) b], st)
      | ReduceResult.incorrectArgument _ => ([finItem prev notReducibleA b], st)
      | ReduceResult.noReduce =>
          if isEmbeddedOp x' then ([{ stack := atomToStack x' prev, bnd := b }], st)
          else queryOp env st prev x' b
  | _ =>
      if isEmbeddedOp x' then ([{ stack := atomToStack x' prev, bnd := b }], st)
      else queryOp env st prev x' b

/-- `(unify <atom> <pattern> <then> <else>)` (Rust `unify`): each match of `atom` against
    `pattern` yields `then` under the merged bindings. If nothing matches, yields `else`. -/
def unifyOp (prev : Stack) (a p t e : Atom) (b : Bindings) : List Item :=
  let ms := (matchAtoms a p).flatMap (fun mb =>
    (Bindings.merge b mb).filterMap (fun m =>
      if Bindings.hasLoop m then none else some (finItem prev (instantiate m t) m)))
  if ms.isEmpty then [finItem prev e b] else ms

/-- Return `true` if the item is a finished final result (a single finished frame with no parent). -/
def isFinal : Item → Bool
  | ⟨[f], _⟩ => f.fin
  | _ => false

/-- Extract the result atom and bindings from a final item. Bindings are retained so a
    sub-evaluation can propagate query-variable solutions (e.g. `$a = A`) to sibling expression
    elements. Hyperon threads these through its mutable stack; here they are threaded explicitly. -/
def finalPair : Item → Atom × Bindings
  | ⟨f :: _, b⟩ => (instantiate b f.atom, b)
  | ⟨[], _⟩ => (emptyA, [])

/-- Surface an unfinished item as a `StackOverflow` error when fuel runs out, so exhausted
    branches are reported rather than silently dropped.
    Limitation: the in-progress atom shown in the error is the top frame, which may be deep
    inside a sub-evaluation and not the user-visible expression that timed out. -/
def exhaustedPair : Item → Atom × Bindings
  | ⟨f :: _, b⟩ => (Atom.expr [Atom.sym "Error", instantiate b f.atom, Atom.sym "StackOverflow"], b)
  | ⟨[], b⟩ => (emptyA, b)

/-- Extract the result atom of a final item with its bindings applied. -/
def finalAtom (it : Item) : Atom := (finalPair it).1

/-- Apply equality-class-aware `instantiate` to `a` under `b` until it reaches a fixpoint, bounded by
    the number of bindings. `instantiate` already follows variable chains and compound values; this
    bounded wrapper preserves the interpreter's explicit fixpoint contract and rejects cycles by
    stabilizing on the unchanged atom. -/
def resolveAtom (b : Bindings) : Nat → Atom → Atom
  | 0, a => a
  | n + 1, a => let a' := instantiate b a; if a' == a then a else resolveAtom b n a'

/-- Raw evaluator-visible projection before canonical binding normalization.
Each requested variable is emitted against its fully resolved value; residual
variable aliases use equality edges, and existing public equalities remain
explicit. -/
def restrictBndRaw (vars : List VarName) (b : Bindings) : Bindings :=
  let solved := vars.filterMap fun x =>
    let v := resolveAtom b (b.length + 1) (Atom.var x)
    match v with
    | Atom.var y =>
        if y == x then none else some (BindingRel.eq x y)
    | _ => some (BindingRel.val x v)
  let eqs := b.filter fun r => match r with
    | BindingRel.eq x y => vars.contains x && vars.contains y
    | _ => false
  solved ++ eqs

/-- Restrict a binding set to the solutions for `vars` (the argument's own query variables), so that
    unrelated internal variables of a sub-evaluation do not leak into the continuation. The raw
    projection is replayed through the ordinary binding merger, ensuring that reachable projections
    have the same canonical representation invariant as every other runtime binding producer. The
    raw fallback preserves total behavior on inconsistent, unreachable API inputs.
    Known issue: an earlier version merely filtered to bindings touching `vars`, which severed
    transitive chains through a dropped intermediate variable and broke b2 recursive backchaining. -/
def restrictBnd (vars : List VarName) (b : Bindings) : Bindings :=
  let raw := restrictBndRaw vars b
  (Bindings.merge [] raw).head?.getD raw

/-- Collect the variables still live in the continuation `prev` after applying current bindings.
    These are the variables a sub-evaluation should retain solutions for (Hyperon `apply_and_retain`).
    A solution `$a = A` propagates to a sibling only if `$a` occurs in the continuation; variables
    introduced inside the sub-evaluation (e.g. a `let` pattern) do not, and are dropped. -/
def scopeVars (b : Bindings) (prev : Stack) : List VarName :=
  prev.flatMap fun f => Atom.vars (instantiate b f.atom)

/-- Expected-type variables whose assignments remain visible in the immediate
continuation of an embedded `metta` call.  Expression-produced bindings are
owned by `metta-thread`; intersecting here preserves return-gate assignments
without leaking bindings local to the evaluated expression. -/
def embeddedMettaRetentionScope (prev : Stack) (expected : Atom) : List VarName :=
  expected.vars.filter fun name => (varsCopy prev).contains name

/-- Every continuation variable protected while type-casting the result of an
embedded `metta` call.  This is intentionally wider than
`embeddedMettaRetentionScope`: a private type candidate must not capture any
live continuation spelling and thereby change whether the cast succeeds, even
though only expected-type assignments are returned to the continuation. -/
def embeddedMettaCastProtectedScope (prev : Stack) : List VarName :=
  varsCopy prev

/-- Return embedded-`metta` results to their caller.  Each result contributes
only its expected-type assignments still live in the continuation; those are
reconciled with the incoming evaluator theory before the result proceeds. -/
def retainEmbeddedMettaResults (prev : Stack) (incoming : Bindings)
    (expected : Atom) (pairs : List (Atom × Bindings)) : List Item :=
  let visibleScope := embeddedMettaRetentionScope prev expected
  pairs.flatMap fun pair =>
    (Bindings.merge incoming (restrictBnd visibleScope pair.2)).map
      (finItem prev pair.1)

/-- Emit one alternative of `superpose-bind`. A pair produced by `collapse-bind` carries its exact
grounded binding set, which is merged with the bindings at the `superpose-bind` call before the atom
returns. The non-pair fallback preserves the interpreter's non-reducing behavior on manually
constructed inputs outside the published `collapse-bind`/`superpose-bind` protocol. -/
def superposeItems (prev : Stack) (current : Bindings) : Atom → List Item
  | Atom.expr [atom, Atom.gnd (Ground.bindings stored)] =>
      (Bindings.merge (Bindings.restore stored) current).filterMap fun merged =>
        if Bindings.hasLoop merged then none else some (finItem prev atom merged)
  | Atom.expr (atom :: _) => [finItem prev atom current]
  | other => [finItem prev other current]

/-- Cartesian product of a list of result-lists. Used to combine nondeterministic argument evaluations. -/
def cartesian {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (cartesian rest).map fun t => x :: t

mutual
/-- Structural type unification for Hyperon's `match_reducted_types` (`types.rs`).
    `%Undefined%` is a wildcard at every nesting depth: Hyperon's `replace_undefined_types`
    deep-replaces each `%Undefined%` (and only `%Undefined%`) by a wildcard matcher before
    calling `match_atoms`. `Atom` is an ordinary symbol here; only the top-level `matchType`
    treats `Atom` as the gradual top. So `(List Atom)` accepts `(List %Undefined%)` (an untyped
    list) but not `(List Number)`, exactly as Hyperon. Type variables bind at the leaf via
    `matchAtoms`. -/
def matchReduced (tb : Bindings) (expected actual : Atom) : Option Bindings :=
  if expected == Atom.sym "%Undefined%" || actual == Atom.sym "%Undefined%"
  then some tb
  else match expected, actual with
    | Atom.expr es, Atom.expr acts => matchReducedList tb es acts
    | _, _ =>
        -- A public matcher result is loop-free in isolation, but merging it
        -- with bindings accumulated by earlier type children can create a
        -- cross-child dependency cycle.  Filter the complete merged state
        -- before selecting a candidate so every threaded accumulator remains
        -- a satisfiable finite-term binding.
        ((matchAtoms expected actual).flatMap (Bindings.merge tb)).filter
          (fun bindings => !bindings.hasLoop) |>.head?
/-- Pointwise binding-threading companion of `matchReduced` for the children of two type
    expressions. Lengths must agree. -/
def matchReducedList (tb : Bindings) : List Atom → List Atom → Option Bindings
  | [], [] => some tb
  | e :: es, a :: acts => match matchReduced tb e a with
      | some tb' => matchReducedList tb' es acts
      | none => none
  | _, _ => none
end

/-- Unify a parameter type with an actual type, threading type-variable bindings `tb`
    (Hyperon `match_types`, `interpreter.rs:1221`). The gradual top matches immediately and leaves
    bindings untouched: `%Undefined%` or `Atom` on either side (Hyperon checks
    `type1 == ATOM_TYPE_ATOM || type2 == ATOM_TYPE_ATOM`, lines 1224-1225, so a value of meta-type
    `Atom`, e.g. a quoted/unevaluated argument, is accepted against any parameter type).
    Otherwise falls through to the structural `matchReduced`, under which a nested `%Undefined%`
    is still a wildcard (but nested `Atom` is an ordinary symbol), so type variables (`$t`,
    `(List $a)`) bind and parametric signatures stay consistent across the arrow's arguments.
    This gradual-top behaviour is Siek-Taha consistency: reflexive and symmetric but not transitive.
    `Proofs/Gradual.lean` proves both the relation (`Consistent.not_transitive`) and that this
    function inherits it (`matchType_not_transitive`: `Number ~ %Undefined% ~ String` yet
    `matchType ... Number String = none`). -/
def matchType (tb : Bindings) (expected actual : Atom) : Option Bindings :=
  if expected == Atom.sym "%Undefined%" || actual == Atom.sym "%Undefined%"
     || expected == Atom.sym "Atom" || actual == Atom.sym "Atom"
  then some tb
  else matchReduced tb expected actual

/-- Match application argument types left-to-right. A failed argument match
    invalidates this function-type candidate; successful matches preserve the
    complete binding state needed by later parametric arguments. -/
def matchApplicationTypeArguments : Bindings → List Atom → List Atom → Option Bindings
  | bindings, [], [] => some bindings
  | bindings, expected :: expecteds, actual :: actuals =>
      match matchType bindings expected actual with
      | some next => matchApplicationTypeArguments next expecteds actuals
      | none => none
  | _, _, _ => none

/-! ### Capture-avoiding type inference

Upstream Hyperon gives variables returned by each type lookup a fresh hidden
identity.  This model represents identity by a string, so every function and
argument type consumed by one inference fold must receive a distinct spelling.
Otherwise unrelated annotations such as `g : (-> $t A R)` and
`k : (-> $t)` capture by name: `(g b (k))` is rejected, while alpha-renaming
only the inner `$t` makes it succeed.

Freshening happens at the consumption boundary, not in the annotation index.
Consequently unresolved polymorphic variables still escape as variables, but
each inference occurrence gets an independent scope. -/

/-- Every variable spelling that a type-inference boundary must avoid.  The
computed candidate types are included because nested inference may already
have introduced generated names. -/
def typeInferenceAvoid (env : MinEnv) (context : Atom)
    (candidateTypes : List Atom) : List VarName :=
  env.atoms.flatMap Atom.vars ++ context.vars ++
    candidateTypes.flatMap Atom.vars

/-- Give every variable in one selected type candidate a capture-avoiding
spelling for this inference position. -/
def freshenTypeCandidate (avoid : List VarName) (position : Nat)
    (type : Atom) : Atom :=
  renameAllVars (captureAvoidingName avoid position) type

/-- Freshen one selected argument type at each source position.  The avoid
set grows with every result, so private variables from distinct arguments are
disjoint by construction. -/
def freshenArgumentTypes (avoid : List VarName) :
    Nat → List Atom → List Atom
  | _, [] => []
  | position, type :: types =>
      let fresh := freshenTypeCandidate avoid position type
      fresh :: freshenArgumentTypes (avoid ++ fresh.vars)
        (position + 1) types

/-- Return the declared or inferred types of an atom (Hyperon `get_atom_types`, all candidates).
    Grounded literals get their built-in type. A symbol gets its `(: s T)` declarations (possibly
    several, or `%Undefined%` if undeclared, as gradual typing allows). A `(StateValue ...)` handle
    gets `(StateMonad ...)`. An application `(f ...)` gets each of `f`'s arrow return types, with
    type variables instantiated by unifying the declared parameter types against the argument types
    (parametric inference). `%Undefined%` acts as the gradual top. -/
def getTypes (env : MinEnv) : Atom → List Atom
  | Atom.gnd (Ground.int _) => [Atom.sym "Number"]
  | Atom.gnd (Ground.float _) => [Atom.sym "Number"]
  | Atom.gnd (Ground.str _) => [Atom.sym "String"]
  | Atom.gnd (Ground.bool _) => [Atom.sym "Bool"]
  | Atom.gnd (Ground.external typeName _) =>
      -- `external` is the structural host-value lane: its first component is
      -- the intrinsic type tag (the native bridge maps `custom T payload` to
      -- `external T payload`), matching Hyperon's grounded `type_()` result.
      [Atom.sym typeName]
  | Atom.gnd _ => [Atom.sym "Grounded"]
  | Atom.var _ => [Atom.sym "%Undefined%"]
  | Atom.sym s => match env.types.getD s [] with | [] => [Atom.sym "%Undefined%"] | ts => ts
  | Atom.expr [Atom.sym "StateValue", v] =>
      -- `wrapStates` rewrote a state handle to carry its contents; type it as
      -- `(StateMonad <type of contents>)`, matching `(: new-state (-> $t (StateMonad $t)))`.
      -- `getTypes` is nonempty by construction; the default only totalizes `head?`.
      [Atom.expr [Atom.sym "StateMonad", ((getTypes env v).head?).getD (Atom.sym "%Undefined%")]]
  | Atom.expr (f :: args) =>
      -- A direct `(: (e ...) T)` declaration wins over inference (e.g. `(: (A B) PairAB)`).
      match env.exprTypes.filter (fun p => p.1 == Atom.expr (f :: args)) with
      | t :: ts => (t :: ts).map (·.2)
      | [] =>
      -- Otherwise the application's type is each arrow return type of its head, with type variables
      -- instantiated by unifying declared parameter types against the argument types (parametric
      -- inference, e.g. `(new-state 2) : (StateMonad Number)`, `(Cons Z Nil) : (List Nat)`).
      -- Every ordered combination of declared argument types is a distinct
      -- private presentation.  Keeping only each lookup's head loses viable
      -- dependent return types such as `(-> $t $t)` at a multiply-typed
      -- argument.
      let rawArgTypeLists := args.map (getTypes env)
      let rawArgTypeChoices := cartesian rawArgTypeLists
      let allRawArgTypes := rawArgTypeLists.flatMap id
      let rawFunctionTypes := getTypes env f
      let avoid := typeInferenceAvoid env (Atom.expr (f :: args))
        (rawFunctionTypes ++ allRawArgTypes)
      let functionAvoid := avoid ++ allRawArgTypes.flatMap Atom.vars
      let functionTypes := rawFunctionTypes.map
        (freshenTypeCandidate functionAvoid args.length)
      match functionTypes.flatMap (fun t =>
              rawArgTypeChoices.filterMap fun rawArgTs =>
                let argTs := freshenArgumentTypes avoid 0 rawArgTs
                match t with
                | Atom.expr (Atom.sym "->" :: ts) =>
                    -- A bare `(->)` has no return component and is not a
                    -- function type.  Reject it instead of fabricating an
                    -- `%Undefined%` result; `(-> R)` remains a valid nullary
                    -- function because its last component is `R`.
                    match ts.getLast? with
                    | none => none
                    | some ret =>
                        match matchApplicationTypeArguments [] ts.dropLast argTs with
                        | some bindings => some (instantiate bindings ret)
                        | none => none
                | _ => none) with
        | [] => [Atom.sym "%Undefined%"]
        | rs => rs
  | Atom.expr [] => [Atom.sym "%Undefined%"]

/-- One rejected actual type at one argument position.  A single argument may
    contribute several of these because its type lookup is an ordered list. -/
structure TypeCheckArgsError where
  position : Nat
  expected : Atom
  actual : Atom

/-- Full result of checking one function candidate's argument types.  The
    successful case retains both the private type bindings and latent errors
    from other actual types.  Latent errors are discarded only when the whole
    function candidate succeeds; if a later argument or return check fails,
    they remain observable. -/
inductive TypeCheckArgsDetailedOutcome where
  | success (bindings : Bindings) (latentErrors : List TypeCheckArgsError)
  | failure (firstError : TypeCheckArgsError) (moreErrors : List TypeCheckArgsError)

/-- Result of classifying every actual type for one argument.  `selected` is
    the first successful binding presentation, while `failures` retains every
    failed actual in declaration order, including failures after the winner. -/
structure ActualTypeScanOutcome where
  selected : Option Bindings
  failures : List Atom

def scanActualTypes (bindings : Bindings) (expected : Atom) :
    List Atom → ActualTypeScanOutcome
  | [] => ⟨none, []⟩
  | actual :: actuals =>
      let tail := scanActualTypes bindings expected actuals
      match matchType bindings expected actual with
      | some output => ⟨some output, tail.failures⟩
      | none => ⟨tail.selected, actual :: tail.failures⟩

/-- Complete classification of one argument's ordered actual-type list.
    Unlike the compatibility scan above, this retains every successful
    private type presentation. -/
structure ActualTypeBranchScanResult where
  successes : List Bindings
  failures : List Atom

def scanActualTypeBranches (bindings : Bindings) (expected : Atom) :
    List Atom → ActualTypeBranchScanResult
  | [] => ⟨[], []⟩
  | actual :: actuals =>
      let tail := scanActualTypeBranches bindings expected actuals
      match matchType bindings expected actual with
      | some output => ⟨output :: tail.successes, tail.failures⟩
      | none => ⟨tail.successes, actual :: tail.failures⟩

/-- All complete argument-applicability branches plus every failed actual
    diagnostic.  Successful presentations are ordered by argument position
    and actual-type declaration.  Errors from later argument positions
    precede errors from earlier positions, matching the published recursive
    traversal and the reference evaluator. -/
structure TypeCheckArgsBranchResult where
  successes : List Bindings
  errors : List TypeCheckArgsError

/-- Variables visible at the complete application boundary.  Recursive
argument checking receives this list unchanged, so a later argument cannot
freshen a private type variable onto an expected type or an earlier source
argument that is no longer present in the recursive suffix. -/
def applicationTypeInferenceScope (expected : Atom)
    (arguments : List Atom) : List VarName :=
  expected.vars ++ arguments.flatMap Atom.vars

/-- The stable argument-freshening boundary for a seeded application scan.
    Besides the expected type and every source argument, it retains every
    variable live when applicability starts.  Branch-local bindings remain an
    additional dynamic avoidance source at each recursive step. -/
def applicationTypeInferenceScopeFrom (expected : Atom)
    (arguments : List Atom) (initialBindings : Bindings) : List VarName :=
  applicationTypeInferenceScope expected arguments ++ initialBindings.vars

/-- Scope-explicit branch-valued argument checking.  `boundaryScope` is
constant across the recursion; branch-local bindings and the current suffix
remain additional dynamic avoidance sources. -/
def typeCheckArgsBranchesScoped (env : MinEnv) (w : World)
    (argTypes : List Atom) (boundaryScope : List VarName) :
    Nat → Bindings → List Atom → TypeCheckArgsBranchResult
  | _, tb, [] => ⟨[tb], []⟩
  | i, tb, ai :: more =>
      match argTypes[i]? with
      | none => ⟨[tb], []⟩  -- defensive fallback; public candidate scans check arity first
      | some ti0 =>
          let reportedExpected := instantiate tb ti0
          let prepared := typePrep w ai
          let rawActuals := getTypes env prepared
          let avoid := boundaryScope ++ typeInferenceAvoid env
            (Atom.expr (ai :: more)) (argTypes ++ rawActuals) ++ tb.vars
          let actuals := rawActuals.map (freshenTypeCandidate avoid i)
          let checked := scanActualTypeBranches tb ti0 actuals
          let continued := checked.successes.map fun tb' =>
            typeCheckArgsBranchesScoped env w argTypes boundaryScope
              (i + 1) tb' more
          let currentErrors := checked.failures.map fun actual =>
            { position := i + 1, expected := reportedExpected, actual }
          ⟨continued.flatMap (·.successes),
            continued.flatMap (·.errors) ++ currentErrors⟩

/-- Ordinary argument checking protects every source argument.  The expected
result is `%Undefined%` on this lane and contributes no variables. -/
def typeCheckArgsBranches (env : MinEnv) (w : World)
    (argTypes : List Atom) (i : Nat) (tb : Bindings)
    (arguments : List Atom) : TypeCheckArgsBranchResult :=
  typeCheckArgsBranchesScoped env w argTypes
    (applicationTypeInferenceScope (Atom.sym "%Undefined%") arguments)
    i tb arguments

/-- Scope-explicit first-success argument checking.  It threads the first
successful type-variable presentation while retaining every failed actual
type as a latent diagnostic.  Later argument blocks precede earlier blocks;
order within a block is the declaration order returned by `getTypes`. -/
def typeCheckArgsDetailedOutcomeScoped (env : MinEnv) (w : World)
    (argTypes : List Atom) (boundaryScope : List VarName) :
    Nat → Bindings → List Atom → TypeCheckArgsDetailedOutcome
  | _, tb, [] => .success tb []
  | i, tb, ai :: more =>
      match argTypes[i]? with
      | none => .success tb []  -- defensive fallback; public candidate scans check arity first
      | some ti0 =>
          let reportedExpected := instantiate tb ti0
          let prepared := typePrep w ai
          let rawActuals := getTypes env prepared
          let avoid := boundaryScope ++ typeInferenceAvoid env
            (Atom.expr (ai :: more)) (argTypes ++ rawActuals) ++ tb.vars
          let actuals := rawActuals.map (freshenTypeCandidate avoid i)
          let checked := scanActualTypes tb ti0 actuals
          let currentErrors := checked.failures.map fun actual =>
            { position := i + 1, expected := reportedExpected, actual }
          match checked.selected with
          | some tb' =>
              match typeCheckArgsDetailedOutcomeScoped env w argTypes
                  boundaryScope (i + 1) tb' more with
              | .success output laterErrors =>
                  .success output (laterErrors ++ currentErrors)
              | .failure firstError laterErrors =>
                  .failure firstError (laterErrors ++ currentErrors)
          | none =>
              match currentErrors with
              | firstError :: moreErrors => .failure firstError moreErrors
              | [] => .failure
                  { position := i + 1, expected := reportedExpected,
                    actual := Atom.sym "%Undefined%" } []

/-- Compatibility entry point for ordinary candidate selection. -/
def typeCheckArgsDetailedOutcome (env : MinEnv) (w : World)
    (argTypes : List Atom) (i : Nat) (tb : Bindings)
    (arguments : List Atom) : TypeCheckArgsDetailedOutcome :=
  typeCheckArgsDetailedOutcomeScoped env w argTypes
    (applicationTypeInferenceScope (Atom.sym "%Undefined%") arguments)
    i tb arguments

/-- Compatibility view of detailed argument checking.  It intentionally
    forgets latent errors on success and exposes only the first error on
    failure.  Existing metatheory that observes this older boundary remains
    valid, while evaluator selection consumes the detailed result below. -/
inductive TypeCheckArgsOutcome where
  | success (bindings : Bindings)
  | failure (position : Nat) (expected actual : Atom)

/-- Compatibility projection of `typeCheckArgsDetailedOutcome`. -/
def typeCheckArgsOutcome (env : MinEnv) (w : World) (argTypes : List Atom) :
    Nat → Bindings → List Atom → TypeCheckArgsOutcome
  | i, tb, args =>
      match typeCheckArgsDetailedOutcome env w argTypes i tb args with
      | .success output _ => .success output
      | .failure firstError _ =>
          .failure firstError.position firstError.expected firstError.actual

/-- Compatibility projection used by the type metatheory: `none` means success and `some` exposes
    the first rejected argument.  The evaluator itself consumes `typeCheckArgsOutcome` so it never
    loses the successful candidate's private theory. -/
def typeCheckArgs (env : MinEnv) (w : World) (argTypes : List Atom)
    (i : Nat) (tb : Bindings) (args : List Atom) : Option (Nat × Atom × Atom) :=
  match typeCheckArgsOutcome env w argTypes i tb args with
  | .success _ => none
  | .failure position expected actual => some (position, expected, actual)

/-- A function candidate selected by the published ordered scan. -/
structure SelectedFunctionType where
  functionType : Atom
  argumentTypes : List Atom
  returnType : Atom
  typeBindings : Bindings

/-- Candidate failure retained when every function type is inapplicable. -/
inductive FunctionTypeError where
  | incorrectArity
  | badArgument (position : Nat) (expected actual : Atom)

def TypeCheckArgsError.toFunctionTypeError
    (error : TypeCheckArgsError) : FunctionTypeError :=
  .badArgument error.position error.expected error.actual

/-- Published ordered candidate-scan result.  Success stops at the first applicable function;
    exhaustion retains every function error and whether a non-function candidate enables tuple
    interpretation. -/
inductive FunctionTypeScanOutcome where
  | selected (function : SelectedFunctionType)
  | exhausted (errors : List FunctionTypeError) (tupleEligible : Bool)

/-- Candidate failure for a scan performed under a nontrivial expected return type.  Argument and
    arity failures reuse the ordinary scan vocabulary; a return mismatch records the conjunct that
    distinguished otherwise argument-applicable signatures. -/
inductive ExpectedFunctionTypeError where
  | ordinary (error : FunctionTypeError)
  | badReturn (expected actual : Atom)

/-- Result of the expected-return-aware ordered scan used by the embedded `metta` boundary.  This is
    deliberately separate from `FunctionTypeScanOutcome`: ordinary unconstrained evaluation keeps
    its established API and reduction path definitionally unchanged. -/
inductive ExpectedFunctionTypeScanOutcome where
  | selected (function : SelectedFunctionType)
  | exhausted (errors : List ExpectedFunctionTypeError) (tupleEligible : Bool)

/-- Expected-return filtering over every successful argument presentation.
    The first surviving presentation commits the candidate; when none
    survives, every return mismatch is retained in presentation order. -/
structure ExpectedReturnBranchScanResult where
  selected : Option Bindings
  errors : List ExpectedFunctionTypeError

def scanExpectedReturnBranches (expected returnType : Atom) :
    List Bindings → ExpectedReturnBranchScanResult
  | [] => ⟨none, []⟩
  | argumentBindings :: branches =>
      let actualReturn := instantiate argumentBindings returnType
      match matchType argumentBindings expected returnType with
      | some typeBindings => ⟨some typeBindings, []⟩
      | none =>
          let tail := scanExpectedReturnBranches expected returnType branches
          ⟨tail.selected, .badReturn expected actualReturn :: tail.errors⟩

def FunctionTypeError.toAtom (expression : Atom) : FunctionTypeError → Atom
  | .incorrectArity =>
      Atom.expr [Atom.sym "Error", expression, Atom.sym "IncorrectNumberOfArguments"]
  | .badArgument position expected actual =>
      Atom.expr [Atom.sym "Error", expression,
        Atom.expr [Atom.sym "BadArgType", Atom.gnd (Ground.int (Int.ofNat position)),
          expected, actual]]

def FunctionTypeScanOutcome.prependError (error : FunctionTypeError) :
    FunctionTypeScanOutcome → FunctionTypeScanOutcome
  | .selected function => .selected function
  | .exhausted errors tupleEligible => .exhausted (error :: errors) tupleEligible

/-- Prepend one failed function candidate's complete ordered error block. -/
def FunctionTypeScanOutcome.prependErrors (newErrors : List FunctionTypeError) :
    FunctionTypeScanOutcome → FunctionTypeScanOutcome
  | .selected function => .selected function
  | .exhausted errors tupleEligible =>
      .exhausted (newErrors ++ errors) tupleEligible

def FunctionTypeScanOutcome.markTupleEligible :
    FunctionTypeScanOutcome → FunctionTypeScanOutcome
  | .selected function => .selected function
  | .exhausted errors _ => .exhausted errors true

def ExpectedFunctionTypeScanOutcome.prependError (error : ExpectedFunctionTypeError) :
    ExpectedFunctionTypeScanOutcome → ExpectedFunctionTypeScanOutcome
  | .selected function => .selected function
  | .exhausted errors tupleEligible => .exhausted (error :: errors) tupleEligible

/-- Prepend one failed function candidate's complete ordered error block. -/
def ExpectedFunctionTypeScanOutcome.prependErrors
    (newErrors : List ExpectedFunctionTypeError) :
    ExpectedFunctionTypeScanOutcome → ExpectedFunctionTypeScanOutcome
  | .selected function => .selected function
  | .exhausted errors tupleEligible =>
      .exhausted (newErrors ++ errors) tupleEligible

def ExpectedFunctionTypeScanOutcome.markTupleEligible :
    ExpectedFunctionTypeScanOutcome → ExpectedFunctionTypeScanOutcome
  | .selected function => .selected function
  | .exhausted errors _ => .exhausted errors true

/-- Variables that an operator signature must avoid when it is consumed for
    one application.  The complete public application scope is included
    explicitly; `typeInferenceAvoid` adds the live expression, annotation
    environment, and every raw signature candidate. -/
def functionTypeSelectionAvoid (env : MinEnv) (expression : Atom)
    (args : List Atom) (expected : Atom) (rawCandidates : List Atom) :
    List VarName :=
  applicationTypeInferenceScope expected args ++
    typeInferenceAvoid env expression rawCandidates

/-- Extend the public application scope with variable spellings already live
in the evaluator binding.  Signature-private names must avoid both: a collision
with an unrelated live binding would make the later #19 seed merge observable. -/
def functionTypeSelectionAvoiding (env : MinEnv) (expression : Atom)
    (args : List Atom) (expected : Atom) (liveAvoid : List VarName)
    (rawCandidates : List Atom) : List VarName :=
  liveAvoid ++
    functionTypeSelectionAvoid env expression args expected rawCandidates

/-- Live-binding-aware signature freshening used by expected evaluation.
Argument-type candidates use positions `0, …, args.length - 1`; the signature
uses the terminal position `args.length`, so the two generated families are
disjoint by construction. Mapping preserves declaration order and
multiplicity. -/
def freshenFunctionTypeCandidatesAvoiding (env : MinEnv) (expression : Atom)
    (args : List Atom) (expected : Atom) (liveAvoid : List VarName)
    (rawCandidates : List Atom) : List Atom :=
  let avoid := functionTypeSelectionAvoiding env expression args expected
    liveAvoid rawCandidates
  rawCandidates.map (freshenTypeCandidate avoid args.length)

/-- Give every operator signature a private presentation before selection.
This compatibility entry point has no additional live evaluator scope. -/
def freshenFunctionTypeCandidates (env : MinEnv) (expression : Atom)
    (args : List Atom) (expected : Atom) (rawCandidates : List Atom) :
    List Atom :=
  freshenFunctionTypeCandidatesAvoiding env expression args expected []
    rawCandidates

/-- Scan the exact ordered type list for one operator.  This is the single selection boundary used
    by arity checking, argument masks, type errors, tuple eligibility, and return handling. -/
def scanFunctionTypeCandidates (env : MinEnv) (w : World) (expression : Atom)
    (args : List Atom) (allowExtraArgs : Bool) : List Atom → FunctionTypeScanOutcome
  | [] => .exhausted [] false
  | candidate :: candidates =>
      match candidate with
      | Atom.expr (Atom.sym "->" :: signature) =>
          match signature.getLast? with
          | none =>
              FunctionTypeScanOutcome.markTupleEligible
                (scanFunctionTypeCandidates env w expression args allowExtraArgs candidates)
          | some returnType =>
              let argumentTypes := signature.dropLast
              if allowExtraArgs || args.length == argumentTypes.length then
                match typeCheckArgsDetailedOutcome env w argumentTypes 0 [] args with
                | .success typeBindings _ =>
                    FunctionTypeScanOutcome.selected
                      ⟨candidate, argumentTypes, returnType, typeBindings⟩
                | .failure firstError moreErrors =>
                    FunctionTypeScanOutcome.prependErrors
                      ((firstError :: moreErrors).map
                        TypeCheckArgsError.toFunctionTypeError)
                      (scanFunctionTypeCandidates env w expression args allowExtraArgs candidates)
              else
                FunctionTypeScanOutcome.prependError .incorrectArity
                  (scanFunctionTypeCandidates env w expression args allowExtraArgs candidates)
      | _ =>
          FunctionTypeScanOutcome.markTupleEligible
            (scanFunctionTypeCandidates env w expression args allowExtraArgs candidates)

/-- Ordered function-type selection from the same `getTypes` list observed by `get-type` and the
    conformance relation.  Applicability always requires exact call/signature arity. -/
def selectFunctionType (env : MinEnv) (w : World) (operator : Atom)
    (args : List Atom) : FunctionTypeScanOutcome :=
  let expression := Atom.expr (operator :: args)
  scanFunctionTypeCandidates env w expression args false
    (getTypes env (typePrep w operator))

/-- Ordered function-type selection under a concrete expected result type.  A candidate succeeds
    only when its arguments and its instantiated return type are jointly applicable; the resulting
    private type theory is the one shared by argument policy and return policy. -/
def scanFunctionTypeCandidatesForExpected (env : MinEnv) (w : World) (expression : Atom)
    (args : List Atom) (expected : Atom) (allowExtraArgs : Bool) :
    List Atom → ExpectedFunctionTypeScanOutcome
  | [] => .exhausted [] false
  | candidate :: candidates =>
      match candidate with
      | Atom.expr (Atom.sym "->" :: signature) =>
          match signature.getLast? with
          | none =>
              ExpectedFunctionTypeScanOutcome.markTupleEligible
                (scanFunctionTypeCandidatesForExpected env w expression args expected
                  allowExtraArgs candidates)
          | some returnType =>
              let argumentTypes := signature.dropLast
              if allowExtraArgs || args.length == argumentTypes.length then
                let argumentBranches :=
                  typeCheckArgsBranchesScoped env w argumentTypes
                    (applicationTypeInferenceScope expected args) 0 [] args
                let returnBranches :=
                  scanExpectedReturnBranches expected returnType
                    argumentBranches.successes
                match returnBranches.selected with
                | some typeBindings =>
                    ExpectedFunctionTypeScanOutcome.selected
                      ⟨candidate, argumentTypes, returnType, typeBindings⟩
                | none =>
                    ExpectedFunctionTypeScanOutcome.prependErrors
                      (argumentBranches.errors.map (fun error =>
                          .ordinary error.toFunctionTypeError) ++
                        returnBranches.errors)
                      (scanFunctionTypeCandidatesForExpected env w expression args expected
                        allowExtraArgs candidates)
              else
                ExpectedFunctionTypeScanOutcome.prependError (.ordinary .incorrectArity)
                  (scanFunctionTypeCandidatesForExpected env w expression args expected
                    allowExtraArgs candidates)
      | _ =>
          ExpectedFunctionTypeScanOutcome.markTupleEligible
            (scanFunctionTypeCandidatesForExpected env w expression args expected
              allowExtraArgs candidates)

/-- Expected-return-aware candidate scan seeded by the evaluator's current
    bindings, as required by the published applicability algorithm.  A
    candidate which conflicts with a live assignment fails inside the scan,
    so candidate search continues and its diagnostic is retained; compatibility
    is not postponed until after selection has committed. -/
def scanFunctionTypeCandidatesForExpectedFrom (env : MinEnv) (w : World)
    (expression : Atom) (args : List Atom) (expected : Atom)
    (allowExtraArgs : Bool) (initialBindings : Bindings) :
    List Atom → ExpectedFunctionTypeScanOutcome
  | [] => .exhausted [] false
  | candidate :: candidates =>
      match candidate with
      | Atom.expr (Atom.sym "->" :: signature) =>
          match signature.getLast? with
          | none =>
              ExpectedFunctionTypeScanOutcome.markTupleEligible
                (scanFunctionTypeCandidatesForExpectedFrom env w expression args
                  expected allowExtraArgs initialBindings candidates)
          | some returnType =>
              let argumentTypes := signature.dropLast
              if allowExtraArgs || args.length == argumentTypes.length then
                let argumentBranches :=
                  typeCheckArgsBranchesScoped env w argumentTypes
                    (applicationTypeInferenceScopeFrom expected args
                      initialBindings) 0 initialBindings args
                let returnBranches :=
                  scanExpectedReturnBranches expected returnType
                    argumentBranches.successes
                match returnBranches.selected with
                | some typeBindings =>
                    ExpectedFunctionTypeScanOutcome.selected
                      ⟨candidate, argumentTypes, returnType, typeBindings⟩
                | none =>
                    ExpectedFunctionTypeScanOutcome.prependErrors
                      (argumentBranches.errors.map (fun error =>
                          .ordinary error.toFunctionTypeError) ++
                        returnBranches.errors)
                      (scanFunctionTypeCandidatesForExpectedFrom env w expression
                        args expected allowExtraArgs initialBindings candidates)
              else
                ExpectedFunctionTypeScanOutcome.prependError
                  (.ordinary .incorrectArity)
                  (scanFunctionTypeCandidatesForExpectedFrom env w expression args
                    expected allowExtraArgs initialBindings candidates)
      | _ =>
          ExpectedFunctionTypeScanOutcome.markTupleEligible
            (scanFunctionTypeCandidatesForExpectedFrom env w expression args
              expected allowExtraArgs initialBindings candidates)

/-- Expected-return-aware selection whose private signature presentation also
avoids every variable spelling in the live evaluator binding. -/
def selectFunctionTypeForExpectedAvoiding (env : MinEnv) (w : World)
    (operator : Atom) (args : List Atom) (expected : Atom)
    (liveAvoid : List VarName) : ExpectedFunctionTypeScanOutcome :=
  let expression := Atom.expr (operator :: args)
  let rawCandidates := getTypes env (typePrep w operator)
  scanFunctionTypeCandidatesForExpected env w expression args expected
    false
    (freshenFunctionTypeCandidatesAvoiding env expression args expected
      liveAvoid rawCandidates)

/-- Published expected-return-aware selection from the evaluator's current
    binding theory.  The same bindings both seed applicability and protect
    signature-private names from collision. -/
def selectFunctionTypeForExpectedFrom (env : MinEnv) (w : World)
    (operator : Atom) (args : List Atom) (expected : Atom)
    (initialBindings : Bindings) : ExpectedFunctionTypeScanOutcome :=
  let expression := Atom.expr (operator :: args)
  let rawCandidates := getTypes env (typePrep w operator)
  scanFunctionTypeCandidatesForExpectedFrom env w expression args expected
    false initialBindings
    (freshenFunctionTypeCandidatesAvoiding env expression args expected
      initialBindings.vars rawCandidates)

/-- Expected-return-aware selection compatibility entry point with no
additional live evaluator scope. -/
def selectFunctionTypeForExpected (env : MinEnv) (w : World) (operator : Atom)
    (args : List Atom) (expected : Atom) : ExpectedFunctionTypeScanOutcome :=
  selectFunctionTypeForExpectedAvoiding env w operator args expected []

/-- Compute which arguments to evaluate from the already-selected function type. -/
def argMask (selected : SelectedFunctionType) (arity : Nat) : List Bool :=
  (List.range arity).map fun i => match selected.argumentTypes[i]? with
    | some rawType =>
        let type := instantiate selected.typeBindings rawType
        type != Atom.sym "Atom" && type != Atom.sym "Variable" &&
          type != Atom.sym "Expression"
    | none => true

/-- Whether the selected function's theory-instantiated return type is `Atom`. -/
def returnsAtom (selected : SelectedFunctionType) : Bool :=
  instantiate selected.typeBindings selected.returnType == Atom.sym "Atom"

/-- Expected type carried by each selected argument policy.  Public selection is strict-arity, so
    a missing formal is only a defensive fallback for direct low-level callers. -/
def argumentEvaluationPolicies (selected : SelectedFunctionType) (arity : Nat) :
    List (Bool × Atom) :=
  (List.range arity).map fun i => match selected.argumentTypes[i]? with
    | some rawType =>
        let type := instantiate selected.typeBindings rawType
        (type != Atom.sym "Atom" && type != Atom.sym "Variable" &&
          type != Atom.sym "Expression", type)
    | none => (true, Atom.sym "%Undefined%")

/-- The expected type for recursively evaluating a selected result.  `Expression` is a quoting
    policy, not a demand that every eventual normal form remain syntactically an expression. -/
def selectedResultExpected (selected : SelectedFunctionType) : Atom :=
  let type := instantiate selected.typeBindings selected.returnType
  if type == Atom.sym "Expression" then Atom.sym "%Undefined%" else type

/-- Variables whose applicability assignments remain observable after the
    caller binding has already been applied to an expected application.  An
    equality-only caller class is represented by the variable that survives
    instantiation, so the post-instantiation expression and expected type are
    the complete public scope. -/
def expectedApplicationVisibleScope (expression expected : Atom) : List VarName :=
  (expected.vars ++ expression.vars).eraseDups

/-- Retain exactly the selected type assignments visible to the caller of an
    expected application.  Fresh signature and argument-type variables are
    excluded by the selection boundary's capture-avoidance contract. -/
def selectedApplicationVisibleBindings (expression expected : Atom)
    (selected : SelectedFunctionType) : Bindings :=
  restrictBnd (expectedApplicationVisibleScope expression expected)
    selected.typeBindings

/-- Merge the caller binding with every visible assignment in one selected
    type theory.  This boundary is shared by applicability and the subsequent
    operator-head cast: both produce private presentations, while only their
    consequences on the post-instantiation application scope may seed
    evaluation. -/
def selectedApplicationInitialBindingsFromTheory (incoming : Bindings)
    (expression expected : Atom) (theory : Bindings) : List Bindings :=
  Bindings.merge incoming
    (restrictBnd (expectedApplicationVisibleScope expression expected) theory)

/-- Merge the caller binding with every visible applicability assignment.
    A successful merge is one initial binding for the complete selected
    application; an inconsistent merge contributes no evaluation branch. -/
def selectedApplicationInitialBindings (incoming : Bindings)
    (expression expected : Atom) (selected : SelectedFunctionType) :
    List Bindings :=
  selectedApplicationInitialBindingsFromTheory incoming expression expected
    selected.typeBindings

/-- Compatibility projection for theorem statements about a single application.  The evaluator
    consumes the complete scan result and therefore preserves all errors. -/
def typeMismatch (env : MinEnv) (w : World) (op : String)
    (args : List Atom) : Option (Nat × Atom × Atom) :=
  match selectFunctionType env w (Atom.sym op) args with
  | .selected _ => none
  | .exhausted _ true => none
  | .exhausted errors false => errors.findSome? fun
      | .badArgument position expected actual => some (position, expected, actual)
      | .incorrectArity => none

/-- Compatibility projection: true exactly when every retained failure is an arity failure and no
    tuple candidate is available.  Runtime evaluation consumes the complete scan instead. -/
def arityMismatch (env : MinEnv) (op : String) (args : List Atom) : Bool :=
  match selectFunctionType env World.empty (Atom.sym op) args with
  | .selected _ => false
  | .exhausted _ true => false
  | .exhausted errors false => !errors.isEmpty && errors.all fun
      | .incorrectArity => true
      | .badArgument _ _ _ => false

/-! ### Reflective `metta` type boundary

The embedded `metta` instruction carries an expected type and a selected
space.  These operands are semantic: the published evaluator casts atoms
against the expected type and evaluates expressions in the selected space.
Keeping this check at the instruction boundary also leaves ordinary
`mettaEval` calls unchanged. -/

/-- First successful expected/actual type match, or every rejected actual
type in source order. -/
def matchExpectedType (bindings : Bindings) (expected : Atom) :
    List Atom → Sum (List Atom) Bindings
  | [] => .inl []
  | actual :: actuals =>
      match matchType bindings expected actual with
      | some output => .inr output
      | none =>
          match matchExpectedType bindings expected actuals with
          | .inr output => .inr output
          | .inl rejected => .inl (actual :: rejected)

/-- Variables that a type candidate must avoid when it is consumed by
    `type_cast`.  Hyperon keeps variables from stored annotations private;
    the string representation used here realizes that identity discipline by
    freshening against the complete live cast boundary. -/
def typeCastInferenceAvoid (env : MinEnv) (prepared atom expected : Atom)
    (bindings : Bindings) (rawTypes : List Atom) : List VarName :=
  expected.vars ++ atom.vars ++ bindings.vars ++
    typeInferenceAvoid env prepared rawTypes

/-- Type-cast one prepared atom while keeping an enclosing evaluator scope
private from the freshly localized type candidates.  The protected scope is
prepended to the ordinary cast boundary because freshening order is observable
through generated names. -/
def mettaTypeCastAvoiding (protectedScope : List VarName) (env : MinEnv)
    (world : World) (bindings : Bindings)
    (atom expected : Atom) : Sum (List Atom) Bindings :=
  let prepared := typePrep world atom
  let rawTypes := getTypes env prepared
  let avoid := protectedScope ++
    typeCastInferenceAvoid env prepared atom expected bindings rawTypes
  matchExpectedType bindings expected
    (freshenArgumentTypes avoid 0 rawTypes)

/-- Type-cast one prepared atom at its own local boundary. -/
def mettaTypeCast (env : MinEnv) (world : World) (bindings : Bindings)
    (atom expected : Atom) : Sum (List Atom) Bindings :=
  mettaTypeCastAvoiding [] env world bindings atom expected

/-- Structured published `BadType` result. -/
def badTypeAtom (source expected actual : Atom) : Atom :=
  Atom.expr [Atom.sym "Error", source,
    Atom.expr [Atom.sym "BadType", expected, actual]]

/-- Complete one non-expression embedded-`metta` cast.  A successful cast
returns its caller-visible binding consequences through the same projection
used by expression results; a failed cast retains the caller binding on every
ordered `BadType` diagnostic. -/
def finishEmbeddedMettaCast (prev : Stack) (incoming : Bindings)
    (atom expected : Atom) : Sum (List Atom) Bindings → List Item
  | .inr output =>
      retainEmbeddedMettaResults prev incoming expected [(atom, output)]
  | .inl rejected =>
      rejected.map fun actual =>
        finItem prev (badTypeAtom atom expected actual) incoming

def ExpectedFunctionTypeError.toAtom (expression : Atom) :
    ExpectedFunctionTypeError → Atom
  | .ordinary error => error.toAtom expression
  | .badReturn expected actual => badTypeAtom expression expected actual

def matchConjAvoiding
    (atoms : List Atom) (patternVars : List VarName) :
    List Atom → St → List Bindings → (List Bindings × St)
  | [], st, sols => (sols, st)
  | p :: ps, st, sols =>
      let (sols', st') := sols.foldl (fun (acc : List Bindings × St) b =>
        -- Thread bindings from earlier conjuncts into this pattern so a query variable pinned by
        -- a previous conjunct (e.g. `$x = Sam` from `(Frog $x)`) is substituted before matching.
        -- Without this it would re-bind against a freshened stored variable (`$x |-> $x#k`) with
        -- no link back to its value, leaking spurious un-instantiated solutions (a3).
        let pInst := instantiate b p
        let avoid := b.vars ++ patternVars
        let (ext, st2) := atoms.foldl (fun (a2 : List Bindings × St) atom =>
          let (renamed, nextCounter) := freshenRuleAvoiding a2.2.counter avoid atom atom
          let atom' := renamed.1
          let more := (matchAtoms pInst atom').flatMap fun mb =>
            (Bindings.merge b mb).filter (fun m => !Bindings.hasLoop m)
          (a2.1 ++ more, { a2.2 with counter := nextCounter })) ([], acc.2)
        (acc.1 ++ ext, st2)) ([], st)
      matchConjAvoiding atoms patternVars ps st' sols'

/-- Conjunctively match a list of patterns over `atoms`, threading bindings from earlier conjuncts
into later ones (Hyperon's `(match S (, p1 ... pk) tmpl)`). Every stored atom is alpha-renamed away
from all query variables and the current branch bindings before matching. Returns the surviving
solution bindings and the advanced gensym counter. -/
def matchConj (atoms patterns : List Atom) (st : St) (sols : List Bindings) :
    List Bindings × St :=
  matchConjAvoiding atoms (patterns.flatMap Atom.vars) patterns st sols

/-- Build the `@doc-formal` record for `atom` from its `(@doc atom ...)` facts and declared type,
    or return `Empty` if undocumented (Hyperon's `get-doc`, g1_docs). A 3-element
    `(@doc a (@desc ...))` is an atom-kind entry. A 5-element
    `(@doc a (@desc ...) (@params ...) (@return ...))` is a function-kind entry; parameter and
    return descriptions are paired with the arrow type's argument/return types, or `%Undefined%`
    when the type is absent or not an arrow of the right arity. -/
def getDocOf (env : MinEnv) (w : World) (atom : Atom) : Atom :=
  let atoms := env.atoms ++ w.selfExtra
  -- Missing documentation types intentionally display `%Undefined%`.
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
            -- The length guard implies `rest` is nonempty; the default is
            -- unreachable and only totalizes `getLast?`.
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

/-- The first evaluated argument that changed into `Empty` or an error.
An argument that was already the same terminal atom is quoted data and does
not stop its branch. -/
@[simp] def firstChangedArgumentStop
    (evaluated source : List Atom) : Option (Atom × Atom) :=
  (evaluated.zip source).find? fun pair =>
    (pair.1 == emptyA || pair.1.isError) && pair.1 != pair.2

/-- Evaluate one symbol-headed application after the ordered type scan has selected its argument
    mask and return policy.  The recursive evaluator and reducer are parameters so this control-flow
    combinator remains outside their well-founded mutual recursion. -/
def evaluateSelectedApplication
    (evalRecursive : St → Bindings → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (args : List Atom)
    (mask : List Bool) (returnAtom : Bool) : List (Atom × Bindings) × St :=
  let queryVars := args.flatMap Atom.vars
  let (partials, st1) := (args.zip mask).foldl
    (fun (acc : List (List Atom × Bindings) × St) ae =>
      acc.1.foldl (fun (acc2 : List (List Atom × Bindings) × St) part =>
        match firstChangedArgumentStop part.1 args with
        | some _ => (acc2.1 ++ [part], acc2.2)
        | none =>
            if ae.2 then
              let (results, st') := evalRecursive acc2.2 part.2 ae.1
              (acc2.1 ++ results.map (fun result =>
                (part.1 ++ [result.1], restrictBnd queryVars
                  ((Bindings.merge part.2 result.2).head?.getD result.2))), st')
            else
              (acc2.1 ++ [(part.1 ++ [instantiate part.2 ae.1], part.2)], acc2.2))
        ([], acc.2))
    ([([], [])], st)
  partials.foldl
    (fun (acc : List (Atom × Bindings) × St) part =>
      match firstChangedArgumentStop part.1 args with
      | some (error, _) => (acc.1 ++ [(error, part.2)], acc.2)
      | none =>
          let application := Atom.expr (Atom.sym op :: part.1)
          let (pairs, st') := reduceApplication acc.2 application
          let (out, st'') := pairs.foldl
            (fun (inner : List (Atom × Bindings) × St) result =>
              let retained := restrictBnd queryVars
                ((Bindings.merge part.2 result.2).head?.getD result.2)
              if result.1 == notReducibleA || result.1 == application then
                (inner.1 ++ [(application, part.2)], inner.2)
              else if returnAtom then
                (inner.1 ++ [(result.1, retained)], inner.2)
              else
                let (more, st3) := evalRecursive inner.2 retained result.1
                (inner.1 ++ more.map (fun next =>
                  (next.1, restrictBnd queryVars
                    ((Bindings.merge retained next.2).head?.getD next.2))), st3))
            ([], st')
          (acc.1 ++ out, st''))
    ([], st1)

/-- Variables retained by the expected-aware application worker.  Existing
argument-variable order stays first so the ordinary empty-seed path is
unchanged; variables already constrained by the selected public seed are
appended once, preserving the published binding-threading contract without
retaining unrelated variables produced inside recursive calls. -/
def expectedApplicationRetentionScope
    (initialBindings : Bindings) (args : List Atom) : List VarName :=
  let queryVars := args.flatMap Atom.vars
  match initialBindings with
  | [] => queryVars
  | _ :: _ =>
      queryVars ++ initialBindings.vars.filter fun name =>
        !queryVars.contains name

/-- Evaluate one selected application from one applicability-produced binding
    while carrying the expected type owned by every evaluated argument and by
    the selected result.  The same initial binding seeds argument evaluation
    and the eventual rule reduction, matching the published
    `interpret_function` boundary. -/
def evaluateExpectedApplicationFrom
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (initialBindings : Bindings)
    (st : St) (op : String) (args : List Atom)
    (selected : SelectedFunctionType) : List (Atom × Bindings) × St :=
  let queryVars := expectedApplicationRetentionScope initialBindings args
  let policies := argumentEvaluationPolicies selected args.length
  let (partials, st1) := (args.zip policies).foldl
    (fun (acc : List (List Atom × Bindings) × St) ae =>
      acc.1.foldl (fun (acc2 : List (List Atom × Bindings) × St) part =>
        match firstChangedArgumentStop part.1 args with
        | some _ => (acc2.1 ++ [part], acc2.2)
        | none =>
            if ae.2.1 then
              let (results, st') := evalRecursive acc2.2 part.2 ae.1 ae.2.2
              (acc2.1 ++ results.map (fun result =>
                (part.1 ++ [result.1], restrictBnd queryVars
                  ((Bindings.merge part.2 result.2).head?.getD result.2))), st')
            else
              (acc2.1 ++ [(part.1 ++ [instantiate part.2 ae.1], part.2)], acc2.2))
        ([], acc.2))
    ([([], initialBindings)], st)
  partials.foldl
    (fun (acc : List (Atom × Bindings) × St) part =>
      match firstChangedArgumentStop part.1 args with
      | some (error, _) => (acc.1 ++ [(error, part.2)], acc.2)
      | none =>
          let application := Atom.expr (Atom.sym op :: part.1)
          let (pairs, st') := reduceApplication acc.2 application
          let (out, st'') := pairs.foldl
            (fun (inner : List (Atom × Bindings) × St) result =>
              let retained := restrictBnd queryVars
                ((Bindings.merge part.2 result.2).head?.getD result.2)
              if result.1 == notReducibleA || result.1 == application then
                (inner.1 ++ [(application, part.2)], inner.2)
              else if returnsAtom selected then
                (inner.1 ++ [(result.1, retained)], inner.2)
              else
                let (more, st3) := evalRecursive inner.2 retained result.1
                  (selectedResultExpected selected)
                (inner.1 ++ more.map (fun next =>
                  (next.1, restrictBnd queryVars
                    ((Bindings.merge retained next.2).head?.getD next.2))), st3))
            ([], st')
          (acc.1 ++ out, st''))
    ([], st1)

/-- Empty-seed compatibility boundary for proofs and low-level callers.
    Runtime entry points use `executeApplicationPlan`, which carries the live
    caller theory through selection, head evaluation, arguments, and reduction. -/
def evaluateExpectedApplication
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : St → Atom → List (Atom × Bindings) × St)
    (st : St) (op : String) (args : List Atom)
    (selected : SelectedFunctionType) : List (Atom × Bindings) × St :=
  evaluateExpectedApplicationFrom evalRecursive reduceApplication [] st op args selected

/-- Evaluate one selected application from every compatible public seed, in
left-to-right order while threading the single runtime state through the
alternatives.  The reducer receives the same seed as argument evaluation, so
the applicability output cannot drift between the two continuations. -/
def evaluateExpectedApplicationSeeds
    (evalRecursive : St → Bindings → Atom → Atom → List (Atom × Bindings) × St)
    (reduceApplication : Bindings → St → Atom → List (Atom × Bindings) × St)
    (initialBindings : List Bindings) (st : St) (op : String)
    (args : List Atom) (selected : SelectedFunctionType) :
    List (Atom × Bindings) × St :=
  initialBindings.foldl
    (fun acc bindings =>
      let (more, nextSt) := evaluateExpectedApplicationFrom evalRecursive
        (reduceApplication bindings) bindings acc.2 op args selected
      (acc.1 ++ more, nextSt))
    ([], st)

/-- Execute the selected half of one application plan.  This is the sole
    runtime boundary between type selection and application evaluation:

    1. evaluate the operator head by casting it against the selected arrow;
    2. project the resulting public theory into one or more compatible seeds;
    3. use each seed for both argument evaluation and rule reduction; and
    4. retain only bindings visible at the application boundary.

    Ordinary and expected-aware evaluation differ only in `expected`; both
    enter this function with the same live caller binding. -/
def executeSelectedApplicationPlan
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : Bindings → St → Atom →
      List (Atom × Bindings) × St)
    (env : MinEnv) (incoming : Bindings) (st : St)
    (op : String) (args : List Atom) (expected : Atom)
    (selected : SelectedFunctionType) : List (Atom × Bindings) × St :=
  let expression := Atom.expr (Atom.sym op :: args)
  match mettaTypeCastAvoiding
      (expectedApplicationVisibleScope expression expected)
      env st.world selected.typeBindings (Atom.sym op) selected.functionType with
  | .inl rejected =>
      let seeds :=
        selectedApplicationInitialBindings incoming expression expected selected
      (seeds.flatMap fun bindings =>
        rejected.map fun actual =>
          (badTypeAtom (Atom.sym op) selected.functionType actual, bindings), st)
  | .inr headBindings =>
      let seeds :=
        selectedApplicationInitialBindingsFromTheory incoming expression expected
          headBindings
      evaluateExpectedApplicationSeeds evalRecursive reduceApplication seeds st
        op args selected

/-- Select and execute one symbol-headed application under `expected`.
    Candidate freshening, applicability, operator-head evaluation, argument
    evaluation, reduction, result checking, and public binding projection are
    shared by ordinary (`%Undefined%`) and expected-aware entry points.  Tuple
    fallback remains a separate policy, but consumes the same incoming theory
    and state chronology. -/
def executeApplicationPlan
    (evalRecursive : St → Bindings → Atom → Atom →
      List (Atom × Bindings) × St)
    (reduceApplication : Bindings → St → Atom →
      List (Atom × Bindings) × St)
    (env : MinEnv) (incoming : Bindings) (st : St)
    (op : String) (args : List Atom) (expected : Atom) :
    List (Atom × Bindings) × St :=
  let expression := Atom.expr (Atom.sym op :: args)
  match selectFunctionTypeForExpectedFrom env st.world
      (Atom.sym op) args expected incoming with
  | .selected selected =>
      executeSelectedApplicationPlan evalRecursive reduceApplication env incoming
        st op args expected selected
  | .exhausted errors tupleEligible =>
      let errorResults := errors.map fun error =>
        (error.toAtom expression, incoming)
      if tupleEligible then
        let tupleSelected : SelectedFunctionType :=
          ⟨Atom.sym "%Undefined%", List.replicate args.length (Atom.sym "%Undefined%"),
            expected, incoming⟩
        let (tupleResults, st') :=
          evaluateExpectedApplicationFrom evalRecursive
            (reduceApplication incoming) incoming st op args tupleSelected
        (tupleResults ++ errorResults, st')
      else
        (errorResults, st)

/-- Apply the published evaluator's success-priority boundary without
    changing the state threaded while discovering the alternatives.  If any
    non-error result exists, all errors are latent and therefore suppressed;
    otherwise every error is retained in its discovery order.  `Empty` is a
    success here, matching the published filter, which distinguishes only
    `(Error ...)` atoms. -/
def prioritizeSemanticResults
    (execution : List (Atom × Bindings) × St) :
    List (Atom × Bindings) × St :=
  let successes := execution.1.filter (fun result => !result.1.isError)
  if successes.isEmpty then
    execution
  else
    (successes, execution.2)

mutual

/-- One interpreter step on the top frame (Rust `interpret_stack`). `fuel` bounds the nested
    sub-interpretation in `collapse-bind`. A finished item with no parent is a final result.
    Limitation: fuel is shared with the nested driver, so deeply nested `collapse-bind` calls
    deplete the outer fuel budget. -/
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
      | Atom.expr [Atom.sym "evalc", x, space] =>
          match evalEnvForSpace env st.world (instantiate it.bnd space) with
          | some evalEnv => evalOp evalEnv st prev x it.bnd
          | none => ([finItem prev (errAtom top.atom "expected: (evalc <atom> <space>)") it.bnd], st)
      | Atom.expr [Atom.sym "chain", nested, Atom.var v, templ] =>
          ([{ stack := atomToStack (Subst.apply [(v, nested)] templ) prev, bnd := it.bnd }], st)
      | Atom.expr [Atom.sym "unify", a, p, t, e] => (unifyOp prev a p t e it.bnd, st)
      | Atom.expr [Atom.sym "cons-atom", h, Atom.expr t] => ([finItem prev (Atom.expr (h :: t)) it.bnd], st)
      | Atom.expr [Atom.sym "cons-atom", _, _] =>
          ([finItem prev (errAtom top.atom "cons-atom: expected (cons-atom <head> <expression>)") it.bnd], st)
      | Atom.expr [Atom.sym "decons-atom", Atom.expr (h :: t)] => ([finItem prev (Atom.expr [h, Atom.expr t]) it.bnd], st)
      | Atom.expr [Atom.sym "decons-atom", _] =>
          ([finItem prev (errAtom top.atom "decons-atom: expected (decons-atom <non-empty-expression>)") it.bnd], st)
      | Atom.expr [Atom.sym "context-space"] =>
          ([finItem prev (contextSpaceAtom env.contextName) it.bnd], st)
      | Atom.expr (Atom.sym "get-type" :: args)
      | Atom.expr (Atom.sym "get-type-space" :: args) =>
          -- `(get-type atom)` and `(get-type-space space atom)` query the selected type environment.
          -- The no-space form uses the current program environment; the explicit-space form layers
          -- the requested space's atoms
          -- onto the runtime environment so space-local `(: ...)` declarations are visible.
          --
          -- An ill-typed application has no type: `get-type` returns no results when an argument
          -- violates the operator's declared signature (d1_gadt: `(get-type (+ 5 "4"))` is `()`).
          -- Otherwise the inferred type(s) are returned with grounded operations inside the type
          -- reduced. d3's dependent `(: ConsN (-> $t (VecN $t $x) (VecN $t (+ $x 1))))` makes
          -- `(ConsN "1" NilN) : (VecN String (+ 0 1))`, which must reduce to `(VecN String 1)`
          -- ("the result returned by get-type is reduced"). Reduction is a no-op on grounded-free
          -- types (e.g. `(Vec Number (S (S Z)))`, `Number`), so b5/d1 are unchanged.
          let parsed := match top.atom, args with
            | Atom.expr (Atom.sym "get-type" :: _), [x] => some (env, x)
            | Atom.expr (Atom.sym "get-type-space" :: _), [space, x] =>
                some (typeEnvForSpace env st.world (instantiate it.bnd space), x)
            | _, _ => none
          match parsed with
          | none => ([finItem prev (errAtom top.atom "get-type expects one atom, or get-type-space expects space and atom") it.bnd], st)
          | some (typeEnv, x) =>
          let xi := instantiate it.bnd x
          let emit : St → List Item × St := fun st0 =>
            (getTypes typeEnv (typePrep st.world xi)).foldl (fun (acc : List Item × St) t =>
              let (rs, st2) := mettaEval typeEnv fuel acc.2 it.bnd t
              (acc.1 ++ rs.map (fun p => finItem prev p.1 it.bnd), st2)) ([], st0)
          match xi with
          | Atom.expr (Atom.sym op :: args) =>
              match selectFunctionType typeEnv st.world (Atom.sym op) args with
              | .selected _ => emit st
              | .exhausted errors tupleEligible =>
                  if tupleEligible || errors.isEmpty then emit st else ([], st)
          | Atom.expr (f :: args) =>
              -- Expression-headed application (e.g. partial application `(curry-a + 2)`): no type
              -- if the head's function type rejects an argument
              -- (d2: `(get-type ((curry-a + 2) "S"))` is `()`).
              match selectFunctionType typeEnv st.world f args with
              | .selected _ => emit st
              | .exhausted errors tupleEligible =>
                  if tupleEligible || errors.isEmpty then emit st else ([], st)
          | _ => emit st
      | Atom.expr [Atom.sym "get-doc", x] =>
          -- Documentation lookup (g1_docs): build the `@doc-formal` for the (uninterpreted) atom
          -- from its `(@doc ...)` facts and declared type, or `Empty` if undocumented. The `help!`
          -- grounded op then formats and prints the result.
          ([finItem prev (getDocOf env st.world (instantiate it.bnd x)) it.bnd], st)
      | Atom.expr [Atom.sym "metta", atom, typ, space] =>
          -- Full type-directed evaluation of `atom` (Hyperon's `metta` strategy). The expected type
          -- and selected space are semantic operands: meta-type passthroughs return immediately;
          -- every other atom is cast in the selected type environment before expression evaluation.
          -- Applicability assignments still live in the caller's continuation are retained;
          -- let-local and fresh type-inference variables remain private.  World effects still
          -- thread.
          let atom' := instantiate it.bnd atom
          let typ' := instantiate it.bnd typ
          let space' := instantiate it.bnd space
          match evalEnvForSpace env st.world space' with
          | none =>
              ([finItem prev
                (errAtom (Atom.expr [Atom.sym "metta", atom', typ', space'])
                  "metta expects a space as its third argument") it.bnd], st)
          | some selectedEnv =>
              if atom' == emptyA || atom'.isError then
                ([finItem prev atom' it.bnd], st)
              else if typ' == Atom.sym "Atom" then
                ([finItem prev atom' it.bnd], st)
              else
                let castNonExpression :=
                  (finishEmbeddedMettaCast prev it.bnd atom' typ'
                    (mettaTypeCastAvoiding
                      (embeddedMettaCastProtectedScope prev)
                      selectedEnv st.world it.bnd atom' typ'), st)
                match atom' with
                | Atom.var _ => ([finItem prev atom' it.bnd], st)
                | Atom.sym _ =>
                    if typ' == Atom.sym "Symbol" then
                      ([finItem prev atom' it.bnd], st)
                    else castNonExpression
                | Atom.gnd _ =>
                    if typ' == Atom.sym "Grounded" then
                      ([finItem prev atom' it.bnd], st)
                    else castNonExpression
                | Atom.expr [] =>
                    if typ' == Atom.sym "Expression" then
                      ([finItem prev atom' it.bnd], st)
                    else castNonExpression
                | Atom.expr (_ :: _) =>
                    if typ' == Atom.sym "Expression" then
                      ([finItem prev atom' it.bnd], st)
                    else
                      let (pairs, st') :=
                        mettaEvalExpected selectedEnv fuel st it.bnd atom' typ'
                      (retainEmbeddedMettaResults prev it.bnd typ' pairs, st')
      | Atom.expr [Atom.sym "capture", atom] =>
          -- `(capture atom)` (Hyperon `core.rs : CaptureOp`, type `(-> Atom Atom)`): interpret
          -- `atom` in the current space and return its results. The argument is taken quoted;
          -- `capture` evaluates it with `metta`-style full evaluation, local bindings not retained.
          let (pairs, st') := mettaEval env fuel st it.bnd atom
          (pairs.map (fun p => finItem prev p.1 it.bnd), st')
      | Atom.expr [Atom.sym "metta-thread", atom, _typ, _space] =>
          -- Like `metta`, but retains query-variable solutions of `atom` that are still live in the
          -- continuation, threading them to sibling expression elements (Hyperon `interpret_tuple`).
          let (pairs, st') := mettaEval env fuel st it.bnd atom
          (pairs.flatMap (fun p =>
             (Bindings.merge it.bnd (restrictBnd (scopeVars it.bnd prev) p.2)).map (finItem prev p.1)), st')
      | Atom.expr [Atom.sym "match", space, pattern, template] =>
          -- Query `space` for `pattern` (single, or a conjunction `(, p1 ... pk)`), returning
          -- `template` per solution (Rust `match`). `&self` is the user-visible program space,
          -- while prelude/runtime support atoms remain available only to evaluation.
          -- A `bind!`-bound token selects a named space in the world. Stored atoms are freshened so
          -- their variables cannot capture query variables.
          match spaceName st.world (instantiate it.bnd space) with
          | none => ([finItem prev (errAtom top.atom "match expects a space as the first argument") it.bnd], st)
          | some spaceName =>
            let rawSpace :=
              if spaceName == "&self" then env.visibleAtoms ++ st.world.selfExtra ++ st.world.selfImports
              else st.world.spaces.getD spaceName []
            -- Deref state handles in stored atoms, and substitute tokens + deref states in the pattern,
            -- so `match` compares by state content (e3: a pattern `... &state-active` matches a stored
            -- `(= ... (State k))` when both cells hold the same value). Both maps are the identity when
            -- there are no states or tokens, so ordinary spaces (e1/c2/&self KB) are unchanged.
            let spaceAtoms := rawSpace.map (resolveStates st.world)
            let patterns := match subTokens st.world pattern with
              | Atom.expr (Atom.sym "," :: ps) => ps.map (resolveStates st.world)
              | p => [resolveStates st.world p]
            let (sols, st') := matchConj spaceAtoms patterns st [it.bnd]
            (sols.filterMap fun m =>
              if Bindings.hasLoop m then none else some (finItem prev (instantiate m template) m), st')
      | Atom.expr [Atom.sym "superpose-bind", Atom.expr pairs] =>
          (pairs.flatMap (superposeItems prev it.bnd), st)
      | Atom.expr [Atom.sym "collapse-bind", nested] =>
          let (atoms, st') := interpretFuel env fuel st [{ stack := atomToStack nested [], bnd := it.bnd }] []
          ([finItem prev
              (Atom.expr (atoms.map fun p =>
                Atom.expr [p.1, Atom.gnd (Ground.bindings (Bindings.store p.2))]))
              it.bnd], st')
      -- mutable state cells (e2/e3) and named spaces (e1/c2), operating on the threaded `world`
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
          -- Allocate a fresh empty named space and return its handle token. `new-mork-space` is
          -- treated identically to `new-space`: MORK is a storage backend (a high-performance trie)
          -- with no semantic difference, so its observable behaviour under add-atom/remove-atom/match
          -- is the same.
          let (id, st') := st.fresh
          let name := "&space-" ++ toString id
          ([finItem prev (Atom.sym name) it.bnd], st'.mapWorld (·.newSpace name))
      | Atom.expr [Atom.sym "fork-space", s] =>
          -- `(fork-space S)`: allocate a fresh space seeded with a snapshot of S's current atoms.
          -- Atom lists are immutable, so the fork and S evolve independently with no aliasing
          -- (c2's parent/child/grandchild spaces). A non-space argument yields a type error.
          match spaceName st.world (instantiate it.bnd s) with
          | some src =>
              let srcAtoms := if src == "&self" then env.visibleAtoms ++ st.world.selfExtra ++ st.world.selfImports
                              else st.world.spaces.getD src []
              let (id, st') := st.fresh
              let name := "&space-" ++ toString id
              ([finItem prev (Atom.sym name) it.bnd], st'.mapWorld (fun w => (w.newSpace name).appendSpace name srcAtoms))
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "fork-space: not a space") it.bnd], st)
      | Atom.expr [Atom.sym "add-atom", s, a] =>
          -- Added atoms go to `world.selfExtra` for `&self` (both `match &self` and `candidatesW`
          -- consult it), or to the named space in `world.spaces` for any other token.
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
          | some "&self" =>
              let avoid := it.bnd.vars ++ liveStackVars it.stack
              let (atoms, st') := freshenSpaceAtoms st avoid (env.visibleAtoms ++ st.world.selfExtra)
              (atoms.map (fun x => finItem prev x it.bnd), st')
          | some name =>
              let avoid := it.bnd.vars ++ liveStackVars it.stack
              let (atoms, st') := freshenSpaceAtoms st avoid (st.world.spaces.getD name [])
              (atoms.map (fun x => finItem prev x it.bnd), st')
          | none => ([finItem prev (errAtom (instantiate it.bnd s) "get-atoms: not a space") it.bnd], st)
      | Atom.expr [Atom.sym "bind!", tok, val] =>
          -- Bind a token to the (already-evaluated) value; `resolveTok` resolves it on use.
          match instantiate it.bnd tok with
          | Atom.sym t => ([finItem prev (Atom.expr []) it.bnd], st.mapWorld (·.bindTok t (instantiate it.bnd val)))
          | other => ([finItem prev (errAtom other "bind!: token must be a symbol") it.bnd], st)
      | Atom.expr [Atom.sym "import!", space, file] =>
          -- Load a module's atoms (pre-read into `env.imports` by the IO runner) into a space.
          -- For `&self`, extends the evaluator with hidden module atoms (visible to later queries,
          -- but not to `get-atoms &self`). Any other token names a separate space (`&kb`), created
          -- or extended with the module's exported atoms. Returns `()`.
          -- Limitation: a file not present in `env.imports` silently contributes no atoms (the
          -- IO runner must pre-read all imported files before evaluation starts).
          let moduleName? := match instantiate it.bnd file with
            | Atom.sym f => some f
            | _ => none
          match spaceName st.world (instantiate it.bnd space), moduleName? with
          | some "&self", some f =>
              ([finItem prev (Atom.expr []) it.bnd],
                st.mapWorld (fun w => importSelfFuel env 64 f w))
          | some name, some f =>
              let keyLoaded := st.world.hasImport name f
              let fileAtoms := env.imports.getD f []
              let update := fun w =>
                if keyLoaded then w else (w.markImport name f).appendSpace name fileAtoms
              ([finItem prev (Atom.expr []) it.bnd], st.mapWorld update)
          | some "&self", none => ([finItem prev (Atom.expr []) it.bnd], st)
          | some _, none => ([finItem prev (Atom.expr []) it.bnd], st)
          | none, _ => ([finItem prev (errAtom (instantiate it.bnd space) "import!: target is not a space") it.bnd], st)
      | _ =>
          if isEmbeddedOp top.atom then
            ([finItem prev (errAtom top.atom "unsupported minimal op") it.bnd], st)
          else
            ([{ stack := { top with fin := true } :: prev, bnd := it.bnd }], st)
  termination_by 4 * fuel + 3
  decreasing_by all_goals omega

/-- Fuel-bounded interpretation driver (Rust `interpret`'s loop). Processes the work queue until
    it empties or fuel runs out, threading the gensym counter and mutable world throughout.
    Limitation: when fuel hits zero, unfinished items are surfaced as `StackOverflow` errors
    rather than returning partial results; there is no way for a caller to resume. -/
def interpretFuel (env : MinEnv) (fuel : Nat) (st : St) (work : List Item) (done : List (Atom × Bindings)) : List (Atom × Bindings) × St :=
  -- `done` accumulates results with their bindings in reverse so each step is O(1); reversed once
  -- on exit. Bindings are kept so callers can propagate query-variable solutions.
  match fuel, work with
  | _, [] => (done.reverse.filter (fun p => p.1 != emptyA), st)
  | 0, w =>
      let rest := w.map (fun it => if isFinal it then finalPair it else exhaustedPair it)
      ((done.reverse ++ rest).filter (fun p => p.1 != emptyA), st)
  | f + 1, it :: rest =>
      let (results, st') := interpretStack1 env f st it
      let finals := (results.filter isFinal).map finalPair
      let more := results.filter (fun r => !isFinal r)
      interpretFuel env f st' (more ++ rest) (finals.reverse ++ done)
  termination_by 4 * fuel
  decreasing_by all_goals omega

/-- Full MeTTa evaluation (`metta`): evaluate each argument whose declared type is not `Atom`,
    then reduce the resulting application to a fixpoint, treating `NotReducible` as "keep the atom".
    Nondeterministic and fuel-bounded. This is the metta-call loop with type-directed argument
    evaluation on top of the minimal interpreter. It is mutual with `interpretStack1` so the
    `metta` instruction can call back into it. -/
def mettaEval (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings) (a : Atom) : List (Atom × Bindings) × St :=
  match fuel with
  | 0 =>
      -- Fuel exhausted: return a `StackOverflow` error (language spec: "returned by the interpreter
      -- when the stack depth is restricted and maximum depth is reached") rather than the unevaluated
      -- atom, so an exhausted result is distinguishable from a genuine normal form.
      ([(Atom.expr [Atom.sym "Error", instantiate bnd a, Atom.sym "StackOverflow"], bnd)], st)
  | fuel + 1 =>
    let source := instantiate bnd a
    if source == emptyA || source.isError then
      ([(source, bnd)], st)
    else prioritizeSemanticResults <| match source with
    | Atom.expr (Atom.sym op :: args) =>
      executeApplicationPlan
        (fun nextSt nextBindings nextAtom nextExpected =>
          mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
        (fun bindings nextSt application =>
          interpretFuel env (fuel + 1) nextSt
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
               bnd := bindings }] [])
        env bnd st op args (Atom.sym "%Undefined%")
    | Atom.expr (e :: rest) =>
        -- Expression-headed application. First try to reduce the whole expression by an equality
        -- rule: higher-order combinators are defined with expression-headed LHS, e.g.
        -- `(= (((curry $f) $x) $y) ($f $x $y))`, so `(((curry +) 2) 3)` must match that rule and
        -- reduce to `(+ 2 3)` (Hyperon's `interpret_expression` tries function application before
        -- tuple). If no rule fires (data tuples like `(1 2 3)`, partial applications like
        -- `((curry +) 2)`), fall back to element-wise tuple interpretation (`interpret_tuple`),
        -- which keeps bindings made in one element live for its siblings.
        let whole := Atom.expr (e :: rest)
        let (ruleRes, st1) := interpretFuel env (fuel + 1) st
          [{ stack := atomToStack (Atom.expr [Atom.sym "eval", whole]) [], bnd := bnd }] []
        let reduced := ruleRes.filter (fun p => p.1 != whole && p.1 != notReducibleA)
        if reduced.isEmpty then
          let (tupleRes, st2) := interpretFuel env (fuel + 1) st1
            [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                Atom.expr [Atom.sym "interpret-tuple", whole, Atom.sym "&self"]]) [], bnd := bnd }] []
          -- Re-evaluate a tuple result whose head reduced into a new application, e.g.
          -- `((is-socrates) Human)` -> `((curry-a is Socrates) Human)` -> `(is Socrates Human)` -> `True`.
          -- A result identical to the input is a normal-form tuple, kept as-is (no re-eval, no loop).
          tupleRes.foldl (fun (acc : List (Atom × Bindings) × St) p =>
            if p.1 == whole then (acc.1 ++ [p], acc.2)
            else let (more, st') := mettaEval env fuel acc.2 p.2 p.1; (acc.1 ++ more, st')) ([], st2)
        else
          reduced.foldl (fun (acc : List (Atom × Bindings) × St) p =>
            let (more, st') := mettaEval env fuel acc.2 p.2 p.1
            (acc.1 ++ more, st')) ([], st1)
    | w =>
        -- The published `metta` boundary does not reduce bare atoms under an
        -- undefined expected type: symbols and grounded atoms pass the
        -- undefined cast, variables pass by meta-type, and `()` is a
        -- successful empty expression.  Equation reduction begins only for
        -- non-empty expressions.
        ([(w, bnd)], st)
  termination_by 4 * fuel + 1
  decreasing_by all_goals omega

/-- Full evaluation under a concrete expected type.  The ordinary `%Undefined%` case delegates to
    `mettaEval` unchanged.  Expression atoms enter the published conjunctive function-candidate
    scan directly; the boundary type cast is retained only for non-expression atoms.  Recursive
    argument/result evaluation carries the selected signature's instantiated expectations. -/
def mettaEvalExpected (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings)
    (a expected : Atom) : List (Atom × Bindings) × St :=
  if expected == Atom.sym "%Undefined%" then
    mettaEval env fuel st bnd a
  else
    let source := instantiate bnd a
    if source == emptyA || source.isError then
      ([(source, bnd)], st)
    else if expected == Atom.atomType ||
        expected == Atom.typeAtomOfMetaType source.metaType ||
        source.metaType == .variable then
      ([(source, bnd)], st)
    else prioritizeSemanticResults <| match (match source with
      | Atom.expr (_ :: _) => Sum.inr bnd
      | _ => mettaTypeCast env st.world bnd source expected) with
    | .inl rejected =>
        (rejected.map fun actual => (badTypeAtom source expected actual, bnd), st)
    | .inr typedBindings =>
      match fuel with
      | 0 =>
          ([(Atom.expr [Atom.sym "Error", instantiate typedBindings source,
              Atom.sym "StackOverflow"], typedBindings)], st)
      | fuel + 1 =>
        match instantiate typedBindings source with
        | Atom.expr (Atom.sym op :: args) =>
          executeApplicationPlan
            (fun nextSt nextBindings nextAtom nextExpected =>
              mettaEvalExpected env fuel nextSt nextBindings nextAtom nextExpected)
            (fun bindings nextSt application =>
              interpretFuel env (fuel + 1) nextSt
                [{ stack := atomToStack (Atom.expr [Atom.sym "eval", application]) [],
                   bnd := bindings }] [])
            env typedBindings st op args expected
        | Atom.expr (e :: rest) =>
            let whole := Atom.expr (e :: rest)
            let (ruleRes, st1) := interpretFuel env (fuel + 1) st
              [{ stack := atomToStack (Atom.expr [Atom.sym "eval", whole]) [],
                 bnd := typedBindings }] []
            let reduced := ruleRes.filter (fun p => p.1 != whole && p.1 != notReducibleA)
            if reduced.isEmpty then
              let (tupleRes, st2) := interpretFuel env (fuel + 1) st1
                [{ stack := atomToStack (Atom.expr [Atom.sym "eval",
                    Atom.expr [Atom.sym "interpret-tuple", whole, Atom.sym "&self"]]) [],
                   bnd := typedBindings }] []
              tupleRes.foldl (fun (acc : List (Atom × Bindings) × St) p =>
                if p.1 == whole then (acc.1 ++ [p], acc.2)
                else
                  let (more, st') :=
                    mettaEvalExpected env fuel acc.2 p.2 p.1 expected
                  (acc.1 ++ more, st')) ([], st2)
            else
              reduced.foldl (fun (acc : List (Atom × Bindings) × St) p =>
                let (more, st') :=
                  mettaEvalExpected env fuel acc.2 p.2 p.1 expected
                (acc.1 ++ more, st')) ([], st1)
        | w => ([(w, typedBindings)], st)
  termination_by 4 * fuel + 2
  decreasing_by all_goals omega

end

/-- Interpret `atom` under `env` with `fuel` steps, without wrapping in `eval`. -/
def interpretAtom (env : MinEnv) (fuel : Nat) (atom : Atom) : List Atom :=
  (interpretFuel env fuel St.init [{ stack := atomToStack atom [] }] []).1.map (·.1)

/-- Evaluate `atom` under `env` with `fuel` steps, i.e. interpret `(eval atom)`. -/
def evalAtomMin (env : MinEnv) (fuel : Nat) (atom : Atom) : List Atom :=
  interpretAtom env fuel (Atom.expr [Atom.sym "eval", atom])

end Metta.Minimal
