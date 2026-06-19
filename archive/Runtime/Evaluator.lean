import MettaHyperonFull.Operational.Semantics
import MettaHyperonFull.Operational.Minimal
import MettaHyperonFull.StdLib.Nondeterminism
import MettaHyperonFull.StdLib.Control

namespace Metta.Runtime
open Metta

/-- Load one top-level atom: a bang query `(! q)` is enqueued in the input register for
    evaluation, and everything else is asserted into the knowledge base. -/
def loadAtom (s : State) (a : Atom) : State :=
  match a with
  | Atom.expr [Atom.sym "!", q] => State.enqueueInput s q
  | Atom.expr (Atom.sym "!" :: xs) => State.enqueueInput s (Atom.expr xs)
  | _ => State.addKb s a

/-- Load a whole program, preserving source order. Because the reader writes `!` as a prefix,
    a bare `!` symbol followed by an atom (e.g. from `!(double Bob)`) is treated as a bang query. -/
def loadProgram (st : State) : List Atom → State
  | [] => st
  | Atom.sym "!" :: q :: rest => loadProgram (State.enqueueInput st q) rest
  | a :: rest => loadProgram (loadAtom st a) rest

/-- Direct evaluation of a single atom against a context space. -/
def evalAtom (cfg : RuntimeConfig) (ctx : Space) (a : Atom) : List Atom :=
  let st := run cfg { State.empty with input := Space.singleton a, kb := ctx }
  st.output.atoms ++ st.work.atoms

/-- MeTTa-style interpret expression with equality reduction and grounded calls. -/
def interpret (cfg : RuntimeConfig) (ctx : Space) (a : Atom) : List Atom :=
  match a with
  | Atom.expr [Atom.sym "unify", x, p, th, el] => evalUnifyInstr x p th el
  | Atom.expr [Atom.sym "superpose", Atom.expr xs] => xs
  | Atom.expr [Atom.sym "collapse", q] => [Atom.expr (evalAtom cfg ctx q)]
  | Atom.expr [Atom.sym "match", _, p, tmpl] => ctx.transform p tmpl
  | Atom.expr [Atom.sym "let", Atom.var x, v, body] => [Subst.apply [(x,v)] body]
  | Atom.expr [Atom.sym "if", c, th, el] => [Metta.StdLib.ifAtom c th el]
  | _ => evalAtom cfg ctx a

end Metta.Runtime
