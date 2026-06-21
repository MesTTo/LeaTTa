/-
Module: CordialMiners.CMIR.Atom
Layer: CMIR
Purpose: The intermediate representation the protocol extracts to: a MeTTaIL-flavoured atom syntax. An
  atom is a symbol, a number, or an application (an S-expression list of atoms). This is the small,
  serialisable target the coarse facts compile into; the extraction and its lossless round-trip live in
  Extract.MettaIL.
Imports: (none beyond core)
Trusted boundary: none
Main exports: Sexpr
Open obligations: none
-/

namespace CordialMiners

/-- A MeTTaIL atom: a symbol, a natural-number literal, or an application (a list of atoms). This is
    the S-expression target the protocol facts extract into. -/
inductive Sexpr where
  | sym : String → Sexpr
  | num : Nat → Sexpr
  | app : List Sexpr → Sexpr
deriving Repr, Inhabited

end CordialMiners
