import MettaHyperonFull.Operational.State
import MettaHyperonFull.Core.Builtins

namespace Metta

/-- Labels for the small-step semantics: the rule fired on each step. -/
inductive StepKind where
  | query | chain | addAtom | remAtom | output
  deriving Repr, BEq, Inhabited

/-- Find equality-rule reductions of an atom in a space. This captures `(= E $t)` style evaluation. -/
def equalityReductions (space : Space) (a : Atom) : List Atom :=
  space.equalityRules.flatMap (fun p =>
    match matchAtoms p.fst a with
    | [] => []
    | bs => bs.map (fun b => instantiate b p.snd))

/-- One-step `add-atom`/`addAtom`: insert the atom into the knowledge base and emit `()`. -/
def stepAddAtom (s : State) (a : Atom) : State :=
  let call1 := Atom.expr [Atom.sym "add-atom", a]
  let call2 := Atom.expr [Atom.sym "addAtom", a]
  let st := { s with input := Space.removeOne (Space.removeOne s.input call1) call2 }
  State.pushOutput (State.addKb st a) Atom.unit

/-- One-step `remove-atom`/`remAtom`: delete one matching atom from the knowledge base and emit `()`. -/
def stepRemAtom (s : State) (a : Atom) : State :=
  let call1 := Atom.expr [Atom.sym "remove-atom", a]
  let call2 := Atom.expr [Atom.sym "remAtom", a]
  let st := { s with input := Space.removeOne (Space.removeOne s.input call1) call2 }
  State.pushOutput (State.remKb st a) Atom.unit

/-- `some` of the equality-rule reductions of `a`, or `none` when `a` matches no rule's LHS. -/
def equalityStep (kb : Space) (a : Atom) : Option (List Atom) :=
  match equalityReductions kb a with
  | [] => none
  | reds => some reds

mutual

/-- Reduce an atom one step against the knowledge base `kb` and the grounded builtins, or `none`
    when `a` is a normal form (`insensitive` to every rule, arXiv:2305.17218 §3.3). Space-aware
    queries (`transform`, `match`, `get-type`) come first; a strict (`evalArgs`) grounded operator
    reduces its arguments left-to-right before it fires, so nested calls such as `(+ (* 2 3) 4)`
    evaluate; otherwise the user equality rules `(= lhs rhs)` apply. -/
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

/-- Reduce the left-most reducible atom of a list by one step, returning the updated argument
    lists (one per nondeterministic result), or `none` when every element is already a normal form. -/
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

/-- One small step of the four-register machine (arXiv:2305.17218 §3.3). The input register is
    drained first: `add-atom`/`remove-atom` mutate the knowledge base, every other atom is reduced
    and its results enter the workspace (`QUERY`). Once the input is empty the workspace is drained:
    reducible atoms are rewritten in place (`CHAIN`) and normal forms move to output (`OUTPUT`). -/
def smallStep? (cfg : RuntimeConfig) (s : State) : Option (StepKind × State) :=
  match s.input.atoms with
  | a :: _ =>
    match a with
    | Atom.expr [Atom.sym "add-atom", x] => some (StepKind.addAtom, stepAddAtom s x)
    | Atom.expr [Atom.sym "addAtom", x] => some (StepKind.addAtom, stepAddAtom s x)
    | Atom.expr [Atom.sym "remove-atom", x] => some (StepKind.remAtom, stepRemAtom s x)
    | Atom.expr [Atom.sym "remAtom", x] => some (StepKind.remAtom, stepRemAtom s x)
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
