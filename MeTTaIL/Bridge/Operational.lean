-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Bridge.Operational
Layer: Bridge
Purpose: The bridge from LeaTTa's MeTTa to MeTTaIL's GSLT terms. LeaTTa formalizes MeTTa (the
  four-metatype object language `Metta.Atom` in `MettaHyperonFull.Core`) and its operational semantics;
  MeTTaIL formalizes the GSLT meta-language whose terms are `MeTTaIL.AST`. The file embeds the former
  into the latter: a symbol becomes a nullary constructor labelled by the symbol, a variable becomes a
  GSLT variable, an expression becomes a (wild-labelled) applied constructor over the embedded children,
  and a grounded atom becomes a nullary constructor keyed by its payload. So MeTTa's four metatypes map
  to distinguishable GSLT term shapes, which is the precise sense in which MeTTa is a GSLT object
  language. The embedding is injective on the grounded-free fragment, which is why `embed_inj` is stated
  there. Grounded atoms are not embedded injectively because floats are not (`0.0` and `-0.0` key alike,
  `NaN` is not equal to itself, the IEEE-754 caveat LeaTTa documents for `Atom` equality). Mathlib-free.
Imports: MettaHyperonFull.Core.Atom, MeTTaIL.Syntax
Trusted boundary: none
Main exports: groundKey, embed, embedList, gndFree, embed_inj, embedList_inj
Open obligations: the injectivity theorems are stated on the grounded-free fragment; extending them to
  the non-float grounded atoms is future work.
-/
import MettaHyperonFull.Core.Atom
import MeTTaIL.Syntax

namespace MeTTaIL.Bridge

open MeTTaIL

/-- A string key for a grounded payload, injective except on floats (`0.0`/`-0.0` key alike and
    `NaN ≠ NaN`, the IEEE-754 caveat LeaTTa documents for `Atom` equality). The `external` key
    length-prefixes its type string, so the two fields cannot run together (`external "a:b" "c"` and
    `external "a" "b:c"` get distinct keys). -/
def groundKey : Metta.Ground → String
  | .int n => "int:" ++ toString n
  | .float f => "float:" ++ toString f
  | .str s => "str:" ++ s
  | .bool b => "bool:" ++ toString b
  | .unit => "unit"
  | .error e => "error:" ++ e
  | .external t p => "ext:" ++ toString t.length ++ ":" ++ t ++ ":" ++ p

mutual
  /-- Embed a MeTTa atom into a GSLT term. -/
  def embed : Metta.Atom → AST
    | .sym s => .sexp (.id s) []
    | .var x => .var (.base x)
    | .gnd g => .sexp (.listE (.idCat (groundKey g))) []
    | .expr xs => .sexp .wild (embedList xs)
  /-- Embed a list of MeTTa atoms. -/
  def embedList : List Metta.Atom → List AST
    | [] => []
    | a :: as => embed a :: embedList as
end

mutual
  /-- A MeTTa atom with no grounded subterm. -/
  def gndFree : Metta.Atom → Prop
    | .sym _ => True
    | .var _ => True
    | .gnd _ => False
    | .expr xs => gndFreeList xs
  /-- A list of grounded-free atoms. -/
  def gndFreeList : List Metta.Atom → Prop
    | [] => True
    | a :: as => gndFree a ∧ gndFreeList as
end

mutual
  /-- The embedding is injective on grounded-free atoms: distinct grounded-free MeTTa terms embed to
      distinct GSLT terms. -/
  theorem embed_inj : ∀ {a b : Metta.Atom}, gndFree a → gndFree b → embed a = embed b → a = b
    | .gnd _, _, hf, _, _ => by simp [gndFree] at hf
    | .sym _, .gnd _, _, hf, _ => by simp [gndFree] at hf
    | .var _, .gnd _, _, hf, _ => by simp [gndFree] at hf
    | .expr _, .gnd _, _, hf, _ => by simp [gndFree] at hf
    | .sym _, .sym _, _, _, h => by simpa [embed] using h
    | .var _, .var _, _, _, h => by simpa [embed] using h
    | .expr xs, .expr ys, hx, hy, h => by
        simp only [embed, AST.sexp.injEq, true_and] at h
        exact congrArg Metta.Atom.expr (embedList_inj (a := xs) (b := ys) hx hy h)
    | .sym _, .var _, _, _, h => by simp [embed] at h
    | .sym _, .expr _, _, _, h => by simp [embed] at h
    | .var _, .sym _, _, _, h => by simp [embed] at h
    | .var _, .expr _, _, _, h => by simp [embed] at h
    | .expr _, .sym _, _, _, h => by simp [embed] at h
    | .expr _, .var _, _, _, h => by simp [embed] at h
  /-- The list version of `embed_inj`. -/
  theorem embedList_inj : ∀ {a b : List Metta.Atom},
      gndFreeList a → gndFreeList b → embedList a = embedList b → a = b
    | [], [], _, _, _ => rfl
    | _ :: _, _ :: _, ha, hb, h => by
        simp only [embedList, List.cons.injEq] at h
        exact congr (congrArg (· :: ·) (embed_inj ha.1 hb.1 h.1))
                    (embedList_inj ha.2 hb.2 h.2)
    | [], _ :: _, _, _, h => by simp [embedList] at h
    | _ :: _, [], _, _, h => by simp [embedList] at h
end

end MeTTaIL.Bridge
