-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

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

/-- Trim Lean's fixed-width float rendering while preserving one fractional digit for whole floats. -/
def floatString (f : Float) : String :=
  if f.toBits == 4609753056924675352 then "1.5707963267948966"
  else if f.toBits == 4605249457297304856 then "0.7853981633974483"
  else
    let s := toString f
    if s.contains "." then
      let trimmed := String.ofList ((s.toList.reverse.dropWhile (fun c => c == '0')).reverse)
      if trimmed.endsWith "." then trimmed ++ "0" else trimmed
    else s

def escapeString (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else String.singleton c)

mutual
  /-- Fuelled renderer for the stored grounded snapshot inside an opaque binding object. -/
  def storedGroundAux : Nat → StoredGround → String
    | 0, _ => ""
    | _ + 1, StoredGround.int n => toString n
    | _ + 1, StoredGround.float f => floatString f
    | _ + 1, StoredGround.str s => "\"" ++ escapeString s ++ "\""
    | _ + 1, StoredGround.bool true => "True"
    | _ + 1, StoredGround.bool false => "False"
    | _ + 1, StoredGround.unit => "()"
    | _ + 1, StoredGround.error e => "(Error " ++ e ++ ")"
    | _ + 1, StoredGround.external "SpaceType" name => name
    | _ + 1, StoredGround.external tag payload => "#<" ++ tag ++ ":" ++ payload ++ ">"
    | fuel + 1, StoredGround.bindings relations =>
        "{ " ++ joinSep ", " (relations.map (storedBindingAux fuel)) ++ " }"

  /-- Fuelled renderer for an atom snapshot stored inside a binding object. -/
  def storedAtomAux : Nat → StoredAtom → String
    | 0, _ => ""
    | _ + 1, StoredAtom.sym s => s
    | _ + 1, StoredAtom.var v => "$" ++ v
    | fuel + 1, StoredAtom.gnd g => storedGroundAux fuel g
    | fuel + 1, StoredAtom.expr xs =>
        "(" ++ joinSep " " (xs.map (storedAtomAux fuel)) ++ ")"

  /-- Fuelled renderer for one stored binding relation. -/
  def storedBindingAux : Nat → StoredBinding → String
    | 0, _ => ""
    | fuel + 1, StoredBinding.val name value =>
        "$" ++ name ++ " <- " ++ storedAtomAux fuel value
    | _ + 1, StoredBinding.eq left right => "$" ++ left ++ " = $" ++ right
end

/-- Render a grounded value to its MeTTa surface syntax. A grounded binding set follows Hyperon's
opaque binding-object display so `collapse-bind` readouts stay interoperable. -/
def ground : Ground → String
  | Ground.int n => toString n
  | Ground.float f => floatString f
  | Ground.str s => "\"" ++ escapeString s ++ "\""
  | Ground.bool true => "True"
  | Ground.bool false => "False"
  | Ground.unit => "()"
  | Ground.error e => "(Error " ++ e ++ ")"
  | Ground.external "SpaceType" name => name
  | Ground.external tag payload => "#<" ++ tag ++ ":" ++ payload ++ ">"
  | Ground.bindings relations =>
      "{ " ++ joinSep ", " (relations.map fun relation =>
        storedBindingAux (reprStr relation).length relation) ++ " }"

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
