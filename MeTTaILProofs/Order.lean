/-
Module: MeTTaILProofs.Order
Layer: Proofs
Purpose: A verified total order on the MeTTaIL term family, the foundation for canonical-form rewriting
  modulo AC. Following Mathlib's encoding of first-order terms
  (`FirstOrder.Language.Term.listEncode`/`listDecode`), every recursive type is serialised to a
  `List Nat` and given an `Encodable` instance from a left-inverse round-trip, then a `LinearOrder` for
  free via `Encodable.encode_injective` and `LinearOrder.lift'`. Strings, and any already-`Encodable`
  sub-term of a different type, collapse to a single `Nat`, so the recursive decoders only ever recurse
  on a structurally smaller tail of the input (exactly Mathlib's `listDecode` shape); a constructor that
  carries a list of sub-terms uses a count prefix and reclaims its children from the front of the
  decoded suffix with `take`/`drop`. The order laws come for free from `Nat`.
Imports: Mathlib, MeTTaIL.Syntax
Trusted boundary: none (fully proved)
Main exports: instances `Encodable DottedPath`, `LinearOrder DottedPath`, `Encodable Cat`,
  `LinearOrder Cat`, `Encodable Label`, `LinearOrder Label`, `Encodable AST`, `LinearOrder AST`.
Open obligations: none
-/
import Mathlib
import MeTTaIL.Syntax

namespace MeTTaIL

/-! ## Strings as a single natural number

A string becomes one `Nat` by encoding the list of its code points through `Encodable (List Nat)`.
Every name leaf in the term family then occupies exactly one slot in the `List Nat` stream, so the
decoders never have to split a string out of the middle of a list. The decode is made total by
defaulting to the empty string; the round-trip only ever feeds it a valid encoding. -/

/-- Encode a string as a single natural number. -/
def encStr (s : String) : Nat :=
  Encodable.encode (s.toList.map Char.toNat)

/-- Decode a string from a single natural number, defaulting to `""` on a malformed code. -/
def decStr (n : Nat) : String :=
  match (Encodable.decode n : Option (List Nat)) with
  | some l => String.ofList (l.map Char.ofNat)
  | none => ""

@[simp] theorem decStr_encStr (s : String) : decStr (encStr s) = s := by
  unfold decStr encStr
  rw [Encodable.encodek]
  simp only [List.map_map]
  have : (Char.ofNat ∘ Char.toNat) = id := by
    funext c; simp [Function.comp, Char.ofNat_toNat]
  rw [this, List.map_id, String.ofList_toList]

/-! ## `DottedPath`

Tags: `0` for `base`, `1` for `qualified`. `DottedPath` does not nest through a list of itself, so the
decoder is a plain prefix-style parser whose recursion is on the structurally smaller tail. -/

/-- Serialise a dotted path to a `List Nat`. -/
def dpEnc : DottedPath → List Nat
  | .base s => 0 :: encStr s :: []
  | .qualified s rest => 1 :: encStr s :: dpEnc rest

/-- Parse one dotted path off the front of a `List Nat`, returning the remainder. -/
def dpDec : List Nat → Option (DottedPath × List Nat)
  | 0 :: n :: rest => some (.base (decStr n), rest)
  | 1 :: n :: rest =>
      match dpDec rest with
      | some (p, rest') => some (.qualified (decStr n) p, rest')
      | none => none
  | _ => none

theorem dpDec_enc (p : DottedPath) (rest : List Nat) :
    dpDec (dpEnc p ++ rest) = some (p, rest) := by
  induction p generalizing rest with
  | base s => simp [dpEnc, dpDec]
  | qualified s rest ih => simp only [dpEnc, List.cons_append, dpDec, ih, decStr_encStr]

/-- Decode a dotted path from a `List Nat` that encodes exactly one. -/
def dpDecTop (l : List Nat) : Option DottedPath :=
  (dpDec l).map Prod.fst

theorem dpDecTop_enc (p : DottedPath) : dpDecTop (dpEnc p) = some p := by
  unfold dpDecTop
  rw [show dpEnc p = dpEnc p ++ [] from (List.append_nil _).symm, dpDec_enc]
  rfl

instance instEncodableDottedPath : Encodable DottedPath :=
  Encodable.ofLeftInjection dpEnc dpDecTop dpDecTop_enc

instance instLinearOrderDottedPath : LinearOrder DottedPath :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

/-! ## `Cat`

Tags: `0` `idCat`, `1` `listOf`, `2` `arrow`, `3` `prod`. The only non-recursive leaf is the `idCat`
string, encoded as one `Nat`. Following Mathlib's `Term.listDecode`, `catDecAll` decodes the whole
stream into a `List Cat` and recurses only on the tail; each constructor reclaims its sub-categories
from the front of the decoded suffix. `arrow` consumes two, `listOf` one, and `prod` consumes a
count-prefixed run. -/

mutual
  /-- Serialise a single category by natural structural recursion. A constructor's tag is followed by
  its sub-categories' encodings; `prod` adds a count prefix so its run can be reclaimed on decode. -/
  def catEnc : Cat → List Nat
    | .idCat s => 0 :: encStr s :: []
    | .listOf c => 1 :: catEnc c
    | .arrow d c => 2 :: catEnc d ++ catEnc c
    | .prod ds => 3 :: ds.length :: catEncL ds
  /-- Serialise a list of categories by concatenating their encodings. -/
  def catEncL : List Cat → List Nat
    | [] => []
    | c :: cs => catEnc c ++ catEncL cs
end

/-- Decode a whole `List Nat` into the list of categories it encodes, recursing on the tail. A
constructor reclaims its children from the front of the decoded suffix. -/
def catDecAll : List Nat → List Cat
  | [] => []
  | 0 :: n :: rest => .idCat (decStr n) :: catDecAll rest
  | 1 :: rest =>
      match catDecAll rest with
      | c :: cs => .listOf c :: cs
      | [] => []
  | 2 :: rest =>
      match catDecAll rest with
      | d :: c :: cs => .arrow d c :: cs
      | _ => []
  | 3 :: k :: rest =>
      let ds := catDecAll rest
      .prod (ds.take k) :: ds.drop k
  | _ => []

mutual
  /-- Decoding the whole stream after one category's encoding yields that category in front of whatever
  the suffix decodes to. -/
  theorem catDecAll_enc :
      ∀ (c : Cat) (rest : List Nat), catDecAll (catEnc c ++ rest) = c :: catDecAll rest
    | .idCat s, rest => by simp only [catEnc, List.cons_append, catDecAll, List.nil_append,
        decStr_encStr]
    | .listOf c, rest => by simp only [catEnc, List.cons_append, catDecAll, catDecAll_enc c]
    | .arrow d c, rest => by
        simp only [catEnc, List.cons_append, List.append_assoc, catDecAll, catDecAll_enc d,
          catDecAll_enc c]
    | .prod ds, rest => by
        simp only [catEnc, List.cons_append, catDecAll, catDecAll_encL ds,
          List.take_left, List.drop_left]
  /-- Decoding the whole stream after a list of categories' encodings yields that list in front of
  whatever the suffix decodes to. -/
  theorem catDecAll_encL :
      ∀ (cs : List Cat) (rest : List Nat), catDecAll (catEncL cs ++ rest) = cs ++ catDecAll rest
    | [], rest => by simp [catEncL]
    | c :: cs, rest => by
        simp only [catEncL, List.append_assoc, catDecAll_enc c, catDecAll_encL cs, List.cons_append]
end

/-- Decode a category from a `List Nat` that encodes exactly one. -/
def catDecTop (l : List Nat) : Option Cat :=
  (catDecAll l).head?

theorem catDecTop_enc (c : Cat) : catDecTop (catEnc c) = some c := by
  unfold catDecTop
  rw [show catEnc c = catEnc c ++ [] from (List.append_nil _).symm, catDecAll_enc]
  rfl

instance instEncodableCat : Encodable Cat :=
  Encodable.ofLeftInjection catEnc catDecTop catDecTop_enc

instance instLinearOrderCat : LinearOrder Cat :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

/-! ## `Label`

Tags: `0` `id`, `1` `wild`, `2` `listE`, `3` `listCons`, `4` `listOne`. The three list labels carry a
`Cat`, which is already `Encodable`, so it goes in as a single `Nat`. `Label` does not nest through a
list of itself, so the decode is a plain non-recursive parser. -/

/-- Serialise a label to a `List Nat`. -/
def lblEnc : Label → List Nat
  | .id s => 0 :: encStr s :: []
  | .wild => 1 :: []
  | .listE c => 2 :: Encodable.encode c :: []
  | .listCons c => 3 :: Encodable.encode c :: []
  | .listOne c => 4 :: Encodable.encode c :: []

/-- Parse one label off the front of a `List Nat`, returning the remainder. The `Cat` payload is
decoded from its single `Nat`; a malformed code defaults to `idCat ""`. -/
def lblDec : List Nat → Option (Label × List Nat)
  | 0 :: n :: rest => some (.id (decStr n), rest)
  | 1 :: rest => some (.wild, rest)
  | 2 :: n :: rest => some (.listE ((Encodable.decode n).getD (.idCat "")), rest)
  | 3 :: n :: rest => some (.listCons ((Encodable.decode n).getD (.idCat "")), rest)
  | 4 :: n :: rest => some (.listOne ((Encodable.decode n).getD (.idCat "")), rest)
  | _ => none

theorem lblDec_enc (l : Label) (rest : List Nat) :
    lblDec (lblEnc l ++ rest) = some (l, rest) := by
  cases l with
  | id s => simp [lblEnc, lblDec]
  | wild => simp [lblEnc, lblDec]
  | listE c => simp [lblEnc, lblDec, Encodable.encodek]
  | listCons c => simp [lblEnc, lblDec, Encodable.encodek]
  | listOne c => simp [lblEnc, lblDec, Encodable.encodek]

/-- Decode a label from a `List Nat` that encodes exactly one. -/
def lblDecTop (l : List Nat) : Option Label :=
  (lblDec l).map Prod.fst

theorem lblDecTop_enc (l : Label) : lblDecTop (lblEnc l) = some l := by
  unfold lblDecTop
  rw [show lblEnc l = lblEnc l ++ [] from (List.append_nil _).symm, lblDec_enc]
  rfl

instance instEncodableLabel : Encodable Label :=
  Encodable.ofLeftInjection lblEnc lblDecTop lblDecTop_enc

instance instLinearOrderLabel : LinearOrder Label :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

/-! ## `AST`

Tags: `0` `var`, `1` `sexp`, `2` `subst`. The non-recursive payloads (`DottedPath` for `var` and
`subst`, `Label` for `sexp`) are already `Encodable`, so each goes in as a single `Nat`. The recursive
sub-terms flow through the stream: `sexp` carries a count-prefixed run of arguments and `subst` carries
two sub-terms. As with `Cat`, `astDecAll` decodes the whole stream into a `List AST`, recursing on the
tail, and each constructor reclaims its children from the front of the decoded suffix. -/

mutual
  /-- Serialise a single term by natural structural recursion. The single-`Nat` payloads (label,
  dotted paths) sit next to the tag; `sexp` adds a count prefix for its argument run. -/
  def astEnc : AST → List Nat
    | .var p => 0 :: Encodable.encode p :: []
    | .sexp l args => 1 :: Encodable.encode l :: args.length :: astEncL args
    | .subst body repl v => 2 :: Encodable.encode v :: astEnc body ++ astEnc repl
  /-- Serialise a list of terms by concatenating their encodings. -/
  def astEncL : List AST → List Nat
    | [] => []
    | a :: as => astEnc a ++ astEncL as
end

/-- Decode a whole `List Nat` into the list of terms it encodes, recursing on the tail. -/
def astDecAll : List Nat → List AST
  | [] => []
  | 0 :: n :: rest => .var ((Encodable.decode n).getD (.base "")) :: astDecAll rest
  | 1 :: n :: k :: rest =>
      let as := astDecAll rest
      .sexp ((Encodable.decode n).getD .wild) (as.take k) :: as.drop k
  | 2 :: n :: rest =>
      match astDecAll rest with
      | body :: repl :: as => .subst body repl ((Encodable.decode n).getD (.base "")) :: as
      | _ => []
  | _ => []

mutual
  /-- Decoding the whole stream after one term's encoding yields that term in front of whatever the
  suffix decodes to. -/
  theorem astDecAll_enc :
      ∀ (a : AST) (rest : List Nat), astDecAll (astEnc a ++ rest) = a :: astDecAll rest
    | .var p, rest => by
        simp only [astEnc, List.cons_append, astDecAll, List.nil_append, Encodable.encodek,
          Option.getD_some]
    | .sexp l args, rest => by
        simp only [astEnc, List.cons_append, astDecAll, Encodable.encodek, Option.getD_some,
          astDecAll_encL args, List.take_left, List.drop_left]
    | .subst body repl v, rest => by
        simp only [astEnc, List.cons_append, List.append_assoc, astDecAll, Encodable.encodek,
          Option.getD_some, astDecAll_enc body, astDecAll_enc repl]
  /-- Decoding the whole stream after a list of terms' encodings yields that list in front of whatever
  the suffix decodes to. -/
  theorem astDecAll_encL :
      ∀ (as : List AST) (rest : List Nat), astDecAll (astEncL as ++ rest) = as ++ astDecAll rest
    | [], rest => by simp [astEncL]
    | a :: as, rest => by
        simp only [astEncL, List.append_assoc, astDecAll_enc a, astDecAll_encL as, List.cons_append]
end

/-- Decode a term from a `List Nat` that encodes exactly one. -/
def astDecTop (l : List Nat) : Option AST :=
  (astDecAll l).head?

theorem astDecTop_enc (a : AST) : astDecTop (astEnc a) = some a := by
  unfold astDecTop
  rw [show astEnc a = astEnc a ++ [] from (List.append_nil _).symm, astDecAll_enc]
  rfl

instance instEncodableAST : Encodable AST :=
  Encodable.ofLeftInjection astEnc astDecTop astDecTop_enc

instance instLinearOrderAST : LinearOrder AST :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

end MeTTaIL
