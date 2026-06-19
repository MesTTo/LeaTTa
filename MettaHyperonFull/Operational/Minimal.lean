import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- The instruction set of the operational-semantics model (arXiv:2305.17218), as an enum.

    This abstract model's set is close to, but not identical with, the executable kernel's embedded
    operations (`Minimal.isEmbeddedOp`):

      shared:       eval, evalc, chain, unify, cons-atom, decons-atom, function (+ return),
                    collapse-bind, superpose-bind, metta, context-space
      model-only:   call-native   -- a host-call placeholder
      kernel-only:  metta-thread, capture   -- used by the standard library, not modelled here

    `evalMinimal` implements ten of the enum's instructions; `chain`, `metta`, and `call-native`
    have no case and fall through to the identity result. The two layers are related by the
    correspondence proofs at the abstract level, not by an identical instruction list. -/
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

/-- Execute `unify a p then else`: try to unify `a` against pattern `p`. On failure return `el`; on
    success return one instantiated `th` per unifier. -/
def evalUnifyInstr (a p th el : Atom) : List Atom :=
  match matchAtoms a p with
  | [] => [el]
  | bs => bs.map (fun b => instantiate b th)

/-- Execute `chain atom var template`: substitute each result in `results` for `x` in `tmpl`. -/
def chainResults (results : List Atom) (x : VarName) (tmpl : Atom) : List Atom :=
  results.map (fun r => Subst.apply [(x,r)] tmpl)

/-- Dispatch a minimal instruction and return its results. The function is total; unrecognized atoms
    are returned unchanged. Of the enum, `chain`, `metta`, and `call-native` have no case here and
    fall through to the identity case. -/
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
