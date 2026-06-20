/-
Module: MettaHyperonFull.Core.Pretty
Layer: Core
Purpose: Rendering atoms back to MeTTa surface syntax. Symbols print verbatim, variables get a `$`
  prefix, grounded values print in their surface form (numbers, quoted strings, True/False, unit,
  errors, external tags), and expressions print space-separated and parenthesised. Result lists print
  in the bracketed form the runners use. Also gives the ToString instance for Atom.
Imports: MettaHyperonFull.Core.Atom
Trusted boundary: none
Main exports: Pretty.joinSep, Pretty.ground, Pretty.atom, Pretty.atoms, the ToString Atom instance
Open obligations: none
-/
import MettaHyperonFull.Core.Atom

namespace Metta

namespace Pretty

/-- Join strings with `sep` between consecutive elements (no leading or trailing separator). -/
def joinSep : String → List String → String
  | _, [] => ""
  | _, [x] => x
  | sep, x :: xs => x ++ sep ++ joinSep sep xs

/-- Render a grounded value to its MeTTa surface syntax (numbers, quoted strings, `True`/`False`,
    `()`, `(Error …)`, external `#<tag:payload>`). -/
def ground : Ground → String
  | Ground.int n => toString n
  | Ground.float f => toString f
  | Ground.str s => "\"" ++ s ++ "\""
  | Ground.bool true => "True"
  | Ground.bool false => "False"
  | Ground.unit => "()"
  | Ground.error e => "(Error " ++ e ++ ")"
  | Ground.external tag payload => "#<" ++ tag ++ ":" ++ payload ++ ">"

/-- Render an atom to MeTTa surface syntax: symbols verbatim, variables `$`-prefixed, grounded via
    `ground`, expressions space-separated and parenthesised. -/
def atom : Atom → String
  | Atom.sym s => s
  | Atom.var v => "$" ++ v
  | Atom.gnd g => ground g
  | Atom.expr xs => "(" ++ joinSep " " (xs.map atom) ++ ")"

/-- Render a result list as `[a, b, …]`, the form the `--min`/`--oracle` runners print. -/
def atoms (xs : List Atom) : String := "[" ++ joinSep ", " (xs.map atom) ++ "]"

end Pretty

instance : ToString Atom where
  toString := Pretty.atom

end Metta
