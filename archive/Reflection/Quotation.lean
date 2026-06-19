import MettaHyperonFull.Core.Atom

namespace Metta

/-- Quotation keeps an atom literal and prevents reduction until unquoted. -/
def quote (a : Atom) : Atom := Atom.expr [Atom.sym "quote", a]
def unquote? : Atom → Option Atom
  | Atom.expr [Atom.sym "quote", a] => some a
  | _ => none

/-- Meta-level representation of a MeTTa expression as data. -/
def asExpressionData (a : Atom) : Atom := Atom.expr [Atom.sym "Expression", a]

end Metta
