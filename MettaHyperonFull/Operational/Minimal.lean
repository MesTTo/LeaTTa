import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- Minimal MeTTa instructions recognized by the interpreter. -/
inductive MinimalInstr where
  | eval | evalc | chain | unify | deconsAtom | consAtom | function | ret
  | collapseBind | superposeBind | metta | contextSpace | callNative
  deriving Repr, BEq, Inhabited

def minimalInstrOf? : Atom → Option MinimalInstr
  | Atom.sym "eval" => some MinimalInstr.eval
  | Atom.sym "evalc" => some MinimalInstr.evalc
  | Atom.sym "chain" => some MinimalInstr.chain
  | Atom.sym "unify" => some MinimalInstr.unify
  | Atom.sym "decons-atom" => some MinimalInstr.deconsAtom
  | Atom.sym "cons-atom" => some MinimalInstr.consAtom
  | Atom.sym "function" => some MinimalInstr.function
  | Atom.sym "return" => some MinimalInstr.ret
  | Atom.sym "collapse-bind" => some MinimalInstr.collapseBind
  | Atom.sym "superpose-bind" => some MinimalInstr.superposeBind
  | Atom.sym "metta" => some MinimalInstr.metta
  | Atom.sym "context-space" => some MinimalInstr.contextSpace
  | Atom.sym "call-native" => some MinimalInstr.callNative
  | _ => none

/-- `unify a p then else` minimal instruction. -/
def evalUnifyInstr (a p th el : Atom) : List Atom :=
  match matchAtoms a p with
  | [] => [el]
  | bs => bs.map (fun b => instantiate b th)

/-- `chain atom var template`: evaluate atom, bind var in template to each result. -/
def chainResults (results : List Atom) (x : VarName) (tmpl : Atom) : List Atom :=
  results.map (fun r => Subst.apply [(x,r)] tmpl)

/-- Complete minimal-instruction dispatcher. The semantics is total and returns a nondeterministic result list. -/
def evalMinimal (cfg : RuntimeConfig) (ctx : Space) : Atom → List Atom
  | Atom.expr [Atom.sym "unify", a, p, th, el] => evalUnifyInstr a p th el
  | Atom.expr [Atom.sym "cons-atom", h, Atom.expr t] => [Atom.expr (h::t)]
  | Atom.expr [Atom.sym "decons-atom", Atom.expr (h::t)] => [Atom.expr [h, Atom.expr t]]
  | Atom.expr [Atom.sym "collapse-bind", a] => [Atom.expr ((run cfg { State.empty with input := Space.singleton a, kb := ctx }).output.atoms)]
  | Atom.expr [Atom.sym "superpose-bind", Atom.expr xs] => xs
  | Atom.expr [Atom.sym "eval", a] => (run cfg { State.empty with input := Space.singleton a, kb := ctx }).output.atoms
  | Atom.expr [Atom.sym "evalc", a, _] => (run cfg { State.empty with input := Space.singleton a, kb := ctx }).output.atoms
  | Atom.expr [Atom.sym "return", a] => [a]
  | Atom.expr [Atom.sym "function", body] => evalMinimal cfg ctx body
  | Atom.expr [Atom.sym "context-space"] => [Atom.expr ctx.atoms]
  | a => [a]

end Metta
