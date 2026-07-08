-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.RSet
Layer: Semantics
Purpose: The finitary red/black set core from the rset paper, as a checked Lean object.
  A set of one colour may contain ordinary sets of the same colour and atoms supplied by the
  opposite colour. Atoms are sealed sets of the opposite colour, so same-colour membership cannot
  inspect them. The module covers the hereditarily finite core that the rset paper names as the
  first rigorous target before the algebraic-set-theory fixpoint and final-coalgebra construction.
Imports: MeTTaIL.Semantics.KnottedUniverse
Trusted boundary: none
Main exports: RSet, RElem, RSet.empty, RSet.insert, RSet.union, RSet.nest, RElem.atom,
  RElem.dropAtom, RElem.dropSet, RSet.atomsOf, RElem.atomsOf, RSet.renameAtoms,
  RSet.renameAtoms_eq_of_forall_mem_atomsOf, RSet.ExtEq, RSet.extSetoid,
  RSet.extEq_union_comm, RSet.extEq_union_assoc, RSet.extEq_union_idem,
  redBlackSetEquiv, reflectiveUniverse, reflective_redBlackSetSwap,
  reflective_blackRedSetSwap, reflective_redBlackAtomSwap, reflective_blackRedAtomSwap,
  ColourAutomaton, twoColourAutomaton
Open obligations: replace exact-member extensionality with the recursive element quotient needed for
  the FM representation theorem, construct the algebraic-set-theory two-sorted fixpoint, and prove
  the final behaviour coalgebra in the knotted topos.
-/
import MeTTaIL.Semantics.KnottedUniverse

namespace MeTTaIL
namespace RSetModel

open KnottedUniverse

universe u

/-- A colour automaton says which colours may supply atoms for which other colours. -/
structure ColourAutomaton (C : Type u) where
  atomEdge : C → C → Prop

namespace ColourAutomaton

/-- A colour may use atoms from a colour when the automaton has the corresponding edge. -/
def Allows {C : Type u} (A : ColourAutomaton C) (target source : C) : Prop :=
  A.atomEdge target source

end ColourAutomaton

/-- The rset paper's two-state automaton: red atoms are black sets, and black atoms are red sets. -/
def twoColourAutomaton : ColourAutomaton Colour where
  atomEdge c d := d = Colour.swap c

/-- Each colour uses the opposite colour as its atom supply. -/
theorem twoColourAutomaton_allows_swap (c : Colour) :
    twoColourAutomaton.Allows c (Colour.swap c) :=
  rfl

/-- The two-colour rset automaton has no self-loop, so atoms remain opaque within one colour. -/
theorem twoColourAutomaton_no_self_loop (c : Colour) :
    ¬ twoColourAutomaton.Allows c c := by
  cases c <;> simp [ColourAutomaton.Allows, twoColourAutomaton, Colour.swap]

mutual

/-- A hereditarily finite rset of one colour.

The syntax is list-like. Extensional quotienting is a later layer; this file checks the finite
red/black atom discipline that the quotient will respect. -/
inductive RSet : Colour → Type where
  | empty {c : Colour} : RSet c
  | insert {c : Colour} : RElem c → RSet c → RSet c

/-- An element of a coloured rset is either an opaque atom from the other colour, or a set of the
same colour. -/
inductive RElem : Colour → Type where
  | atom {c : Colour} : RSet (Colour.swap c) → RElem c
  | set {c : Colour} : RSet c → RElem c

end

namespace RElem

/-- Seal a set of the opposite colour as an opaque atom. -/
def quoteAtom {c : Colour} (a : RSet (Colour.swap c)) : RElem c :=
  atom a

/-- Open an atom. Same-colour sets are not atoms, so they return `none`. -/
def dropAtom {c : Colour} : RElem c → Option (RSet (Colour.swap c))
  | atom a => some a
  | set _ => none

/-- Open a same-colour nested set. Atoms stay opaque to same-colour membership. -/
def dropSet {c : Colour} : RElem c → Option (RSet c)
  | atom _ => none
  | set s => some s

@[simp] theorem dropAtom_quoteAtom {c : Colour} (a : RSet (Colour.swap c)) :
    dropAtom (quoteAtom a) = some a :=
  rfl

@[simp] theorem dropSet_atom {c : Colour} (a : RSet (Colour.swap c)) :
    dropSet (atom a : RElem c) = none :=
  rfl

@[simp] theorem dropSet_set {c : Colour} (s : RSet c) :
    dropSet (set s : RElem c) = some s :=
  rfl

/-- Dropping a quoted atom and then quoting it again returns the same element. -/
theorem quoteAtom_dropAtom {c : Colour} {e : RElem c} {a : RSet (Colour.swap c)}
    (h : dropAtom e = some a) : quoteAtom a = e := by
  cases e with
  | atom b =>
      cases h
      rfl
  | set s =>
      cases h

end RElem

namespace RSet

/-- Membership in the list-like rset syntax. The extensional quotient is a later layer. -/
inductive Mem {c : Colour} (e : RElem c) : RSet c → Prop where
  | head {tail : RSet c} : Mem e (insert e tail)
  | tail {x : RElem c} {tail : RSet c} : Mem e tail → Mem e (insert x tail)

/-- Add one element to a coloured set. -/
def cons {c : Colour} (e : RElem c) (s : RSet c) : RSet c :=
  insert e s

/-- A singleton coloured set. -/
def singleton {c : Colour} (e : RElem c) : RSet c :=
  insert e RSet.empty

/-- Nest a coloured set as an ordinary same-colour element. -/
def nest {c : Colour} (s : RSet c) : RSet c :=
  singleton (RElem.set s)

/-- Union of list-like finite sets. The extensional quotient will collapse order and duplicates. -/
def union {c : Colour} : RSet c → RSet c → RSet c
  | RSet.empty, t => t
  | insert e s, t => insert e (union s t)

@[simp] theorem not_mem_empty {c : Colour} (e : RElem c) : ¬ Mem e RSet.empty := by
  intro h
  cases h

@[simp] theorem mem_insert_self {c : Colour} (e : RElem c) (s : RSet c) :
    Mem e (insert e s) :=
  Mem.head

/-- Existing members remain members after an insertion. -/
theorem mem_insert_tail {c : Colour} {e x : RElem c} {s : RSet c}
    (h : Mem e s) : Mem e (insert x s) :=
  Mem.tail h

/-- Membership in an inserted element splits into the head case and the old tail. -/
theorem mem_insert_iff {c : Colour} (e x : RElem c) (s : RSet c) :
    Mem e (insert x s) ↔ e = x ∨ Mem e s := by
  constructor
  · intro h
    cases h with
    | head => exact Or.inl rfl
    | tail htail => exact Or.inr htail
  · intro h
    rcases h with rfl | htail
    · exact Mem.head
    · exact Mem.tail htail

/-- Membership in a list-like union is membership in one input. -/
theorem mem_union_iff {c : Colour} :
    ∀ (s t : RSet c) (e : RElem c), Mem e (union s t) ↔ Mem e s ∨ Mem e t
  | RSet.empty, t, e => by
      constructor
      · intro h
        exact Or.inr h
      · intro h
        rcases h with h | h
        · cases h
        · exact h
  | RSet.insert x s, t, e => by
      have ih := mem_union_iff s t e
      constructor
      · intro h
        rcases (mem_insert_iff e x (union s t)).mp h with hhead | htail
        · exact Or.inl ((mem_insert_iff e x s).mpr (Or.inl hhead))
        · rcases ih.mp htail with hs | ht
          · exact Or.inl ((mem_insert_iff e x s).mpr (Or.inr hs))
          · exact Or.inr ht
      · intro h
        rcases h with hs | ht
        · rcases (mem_insert_iff e x s).mp hs with hhead | htail
          · exact (mem_insert_iff e x (union s t)).mpr (Or.inl hhead)
          · exact (mem_insert_iff e x (union s t)).mpr (Or.inr (ih.mpr (Or.inl htail)))
        · exact (mem_insert_iff e x (union s t)).mpr (Or.inr (ih.mpr (Or.inr ht)))
termination_by s _ _ => sizeOf s
decreasing_by
  simp_wf
  omega

/-- Extensional equality for the current finite syntax: the same exact elements occur. -/
def ExtEq {c : Colour} (s t : RSet c) : Prop :=
  ∀ e, Mem e s ↔ Mem e t

/-- Extensional equality is reflexive. -/
theorem extEq_refl {c : Colour} (s : RSet c) : ExtEq s s := by
  intro e
  rfl

/-- Extensional equality is symmetric. -/
theorem extEq_symm {c : Colour} {s t : RSet c} (h : ExtEq s t) : ExtEq t s := by
  intro e
  exact (h e).symm

/-- Extensional equality is transitive. -/
theorem extEq_trans {c : Colour} {s t u : RSet c} (hst : ExtEq s t) (htu : ExtEq t u) :
    ExtEq s u := by
  intro e
  exact (hst e).trans (htu e)

/-- The setoid that quotients the finite syntax by exact-member extensional equality. -/
def extSetoid (c : Colour) : Setoid (RSet c) where
  r := fun s t => ExtEq s t
  iseqv := {
    refl := fun s => extEq_refl s
    symm := fun h => extEq_symm h
    trans := fun hst htu => extEq_trans hst htu
  }

/-- The current extensional quotient of finite rsets. -/
def Extensional (c : Colour) : Type :=
  Quotient (extSetoid c)

/-- Send syntax into the extensional quotient. -/
def toExt {c : Colour} (s : RSet c) : Extensional c :=
  Quotient.mk (extSetoid c) s

/-- Extensionally equal syntax has the same quotient representative. -/
theorem toExt_eq_of_extEq {c : Colour} {s t : RSet c} (h : ExtEq s t) :
    toExt s = toExt t :=
  Quotient.sound h

/-- Union respects extensional equality in both inputs. -/
theorem extEq_union_congr {c : Colour} {s s' t t' : RSet c}
    (hs : ExtEq s s') (ht : ExtEq t t') : ExtEq (union s t) (union s' t') := by
  intro e
  constructor
  · intro h
    rcases (mem_union_iff s t e).mp h with hleft | hright
    · exact (mem_union_iff s' t' e).mpr (Or.inl ((hs e).mp hleft))
    · exact (mem_union_iff s' t' e).mpr (Or.inr ((ht e).mp hright))
  · intro h
    rcases (mem_union_iff s' t' e).mp h with hleft | hright
    · exact (mem_union_iff s t e).mpr (Or.inl ((hs e).mpr hleft))
    · exact (mem_union_iff s t e).mpr (Or.inr ((ht e).mpr hright))

/-- Empty on the left is the identity for union, up to extensional equality. -/
theorem extEq_empty_union {c : Colour} (s : RSet c) : ExtEq (union RSet.empty s) s := by
  intro e
  constructor
  · intro h
    rcases (mem_union_iff RSet.empty s e).mp h with hempty | hs
    · cases hempty
    · exact hs
  · intro h
    exact (mem_union_iff RSet.empty s e).mpr (Or.inr h)

/-- Empty on the right is the identity for union, up to extensional equality. -/
theorem extEq_union_empty {c : Colour} (s : RSet c) : ExtEq (union s RSet.empty) s := by
  intro e
  constructor
  · intro h
    rcases (mem_union_iff s RSet.empty e).mp h with hs | hempty
    · exact hs
    · cases hempty
  · intro h
    exact (mem_union_iff s RSet.empty e).mpr (Or.inl h)

/-- Union is idempotent at the extensional level. -/
theorem extEq_union_idem {c : Colour} (s : RSet c) : ExtEq (union s s) s := by
  intro e
  constructor
  · intro h
    rcases (mem_union_iff s s e).mp h with hs | hs <;> exact hs
  · intro h
    exact (mem_union_iff s s e).mpr (Or.inl h)

/-- Union is commutative at the extensional level. -/
theorem extEq_union_comm {c : Colour} (s t : RSet c) : ExtEq (union s t) (union t s) := by
  intro e
  constructor
  · intro h
    rcases (mem_union_iff s t e).mp h with hs | ht
    · exact (mem_union_iff t s e).mpr (Or.inr hs)
    · exact (mem_union_iff t s e).mpr (Or.inl ht)
  · intro h
    rcases (mem_union_iff t s e).mp h with ht | hs
    · exact (mem_union_iff s t e).mpr (Or.inr ht)
    · exact (mem_union_iff s t e).mpr (Or.inl hs)

/-- Union is associative at the extensional level. -/
theorem extEq_union_assoc {c : Colour} (s t u : RSet c) :
    ExtEq (union (union s t) u) (union s (union t u)) := by
  intro e
  constructor
  · intro h
    rcases (mem_union_iff (union s t) u e).mp h with hst | hu
    · rcases (mem_union_iff s t e).mp hst with hs | ht
      · exact (mem_union_iff s (union t u) e).mpr (Or.inl hs)
      · exact (mem_union_iff s (union t u) e).mpr
          (Or.inr ((mem_union_iff t u e).mpr (Or.inl ht)))
    · exact (mem_union_iff s (union t u) e).mpr
        (Or.inr ((mem_union_iff t u e).mpr (Or.inr hu)))
  · intro h
    rcases (mem_union_iff s (union t u) e).mp h with hs | htu
    · exact (mem_union_iff (union s t) u e).mpr
        (Or.inl ((mem_union_iff s t e).mpr (Or.inl hs)))
    · rcases (mem_union_iff t u e).mp htu with ht | hu
      · exact (mem_union_iff (union s t) u e).mpr
          (Or.inl ((mem_union_iff s t e).mpr (Or.inr ht)))
      · exact (mem_union_iff (union s t) u e).mpr (Or.inr hu)

end RSet

mutual

/-- The opposite-colour atoms occurring in a finite coloured set. -/
def RSet.atomsOf {c : Colour} : RSet c → List (RSet (Colour.swap c))
  | RSet.empty => []
  | RSet.insert e rest => RElem.atomsOf e ++ RSet.atomsOf rest

/-- The opposite-colour atoms occurring in one element. -/
def RElem.atomsOf {c : Colour} : RElem c → List (RSet (Colour.swap c))
  | RElem.atom a => [a]
  | RElem.set s => RSet.atomsOf s

end

mutual

/-- Rename the atom supply of a coloured set. The definition is the finitary permutation-action
skeleton from the rset paper. -/
def RSet.renameAtoms {c : Colour} (ρ : RSet (Colour.swap c) → RSet (Colour.swap c)) :
    RSet c → RSet c
  | RSet.empty => RSet.empty
  | RSet.insert e rest => RSet.insert (RElem.renameAtoms ρ e) (RSet.renameAtoms ρ rest)

/-- Rename atoms inside one element, without looking inside atom interiors. -/
def RElem.renameAtoms {c : Colour} (ρ : RSet (Colour.swap c) → RSet (Colour.swap c)) :
    RElem c → RElem c
  | RElem.atom a => RElem.atom (ρ a)
  | RElem.set s => RElem.set (RSet.renameAtoms ρ s)

end

namespace RSet

/-- A map on atoms supports a set when it fixes every atom occurring in that set. -/
def Supports {c : Colour} (ρ : RSet (Colour.swap c) → RSet (Colour.swap c)) (s : RSet c) :
    Prop :=
  ∀ a, a ∈ s.atomsOf → ρ a = a

/-- Freshness in the finitary rset core is absence from the occurrence support. -/
def Fresh {c : Colour} (a : RSet (Colour.swap c)) (s : RSet c) : Prop :=
  a ∉ s.atomsOf

end RSet

mutual

/-- If a renaming fixes every occurring atom, the finite set is unchanged. The theorem is the checked
finite-support statement for the rset core. -/
theorem RSet.renameAtoms_eq_of_forall_mem_atomsOf {c : Colour}
    (ρ : RSet (Colour.swap c) → RSet (Colour.swap c)) :
    ∀ s : RSet c, (∀ a, a ∈ s.atomsOf → ρ a = a) → RSet.renameAtoms ρ s = s
  | RSet.empty, _ => rfl
  | RSet.insert e rest, h => by
      have he : RElem.renameAtoms ρ e = e :=
        RElem.renameAtoms_eq_of_forall_mem_atomsOf ρ e (by
          intro a ha
          exact h a (by simp [RSet.atomsOf, ha]))
      have hrest : RSet.renameAtoms ρ rest = rest :=
        RSet.renameAtoms_eq_of_forall_mem_atomsOf ρ rest (by
          intro a ha
          exact h a (by simp [RSet.atomsOf, ha]))
      simp [RSet.renameAtoms, he, hrest]

/-- Element form of the finite-support theorem. -/
theorem RElem.renameAtoms_eq_of_forall_mem_atomsOf {c : Colour}
    (ρ : RSet (Colour.swap c) → RSet (Colour.swap c)) :
    ∀ e : RElem c, (∀ a, a ∈ e.atomsOf → ρ a = a) → RElem.renameAtoms ρ e = e
  | RElem.atom a, h => by
      have ha : ρ a = a := h a (by simp [RElem.atomsOf])
      simp [RElem.renameAtoms, ha]
  | RElem.set s, h => by
      have hs : RSet.renameAtoms ρ s = s :=
        RSet.renameAtoms_eq_of_forall_mem_atomsOf ρ s (by
          intro a ha
          exact h a (by simpa [RElem.atomsOf] using ha))
      simp [RElem.renameAtoms, hs]

end

namespace RSet

/-- The support predicate is exactly the hypothesis needed by atom renaming. -/
theorem renameAtoms_eq_of_supports {c : Colour}
    (ρ : RSet (Colour.swap c) → RSet (Colour.swap c)) (s : RSet c)
    (h : Supports ρ s) : RSet.renameAtoms ρ s = s :=
  RSet.renameAtoms_eq_of_forall_mem_atomsOf ρ s h

/-- The identity atom map supports every finite rset. -/
theorem supports_id {c : Colour} (s : RSet c) : Supports id s := by
  intro _ _
  rfl

@[simp] theorem renameAtoms_id {c : Colour} (s : RSet c) :
    RSet.renameAtoms id s = s :=
  renameAtoms_eq_of_supports id s (supports_id s)

end RSet

mutual

/-- Swap a red finite set to the black copy. -/
def redToBlackSet : RSet Colour.red → RSet Colour.black
  | RSet.empty => RSet.empty
  | RSet.insert e rest => RSet.insert (redToBlackElem e) (redToBlackSet rest)

/-- Swap a black finite set to the red copy. -/
def blackToRedSet : RSet Colour.black → RSet Colour.red
  | RSet.empty => RSet.empty
  | RSet.insert e rest => RSet.insert (blackToRedElem e) (blackToRedSet rest)

/-- Swap a red element to the black copy. Red atoms become black sets, and red sets become
black atoms. -/
def redToBlackElem : RElem Colour.red → RElem Colour.black
  | RElem.atom a => RElem.set a
  | RElem.set s => RElem.atom s

/-- Swap a black element to the red copy. -/
def blackToRedElem : RElem Colour.black → RElem Colour.red
  | RElem.atom a => RElem.set a
  | RElem.set s => RElem.atom s

end

/-- Swapping a red set to black and back is the identity. -/
theorem blackToRedSet_redToBlackSet : ∀ s : RSet Colour.red,
    blackToRedSet (redToBlackSet s) = s
  | RSet.empty => by
      simp [redToBlackSet, blackToRedSet]
  | RSet.insert e rest => by
      have hrest : blackToRedSet (redToBlackSet rest) = rest :=
        blackToRedSet_redToBlackSet rest
      cases e <;> simp [redToBlackSet, blackToRedSet, redToBlackElem, blackToRedElem, hrest]
termination_by s => sizeOf s
decreasing_by
  simp_wf
  omega

/-- Swapping a black set to red and back is the identity. -/
theorem redToBlackSet_blackToRedSet : ∀ s : RSet Colour.black,
    redToBlackSet (blackToRedSet s) = s
  | RSet.empty => by
      simp [redToBlackSet, blackToRedSet]
  | RSet.insert e rest => by
      have hrest : redToBlackSet (blackToRedSet rest) = rest :=
        redToBlackSet_blackToRedSet rest
      cases e <;> simp [redToBlackSet, blackToRedSet, redToBlackElem, blackToRedElem, hrest]
termination_by s => sizeOf s
decreasing_by
  simp_wf
  omega

/-- Swapping a red element to black and back is the identity. -/
theorem blackToRedElem_redToBlackElem (e : RElem Colour.red) :
    blackToRedElem (redToBlackElem e) = e := by
  cases e <;> rfl

/-- Swapping a black element to red and back is the identity. -/
theorem redToBlackElem_blackToRedElem (e : RElem Colour.black) :
    redToBlackElem (blackToRedElem e) = e := by
  cases e <;> rfl

/-- The colour swap equivalence on finite rsets. -/
def redBlackSetEquiv : RSet Colour.red ≃ RSet Colour.black where
  toFun := redToBlackSet
  invFun := blackToRedSet
  left_inv := blackToRedSet_redToBlackSet
  right_inv := redToBlackSet_blackToRedSet

/-- The induced colour swap equivalence on atom sorts. -/
def redBlackAtomEquiv : RSet Colour.black ≃ RSet Colour.red where
  toFun := blackToRedSet
  invFun := redToBlackSet
  left_inv := redToBlackSet_blackToRedSet
  right_inv := blackToRedSet_redToBlackSet

/-- The finitary rset core instantiates the red/black reflective-universe interface. Red atoms are
black finite sets, and black atoms are red finite sets. -/
def reflectiveUniverse : ReflectiveUniverse where
  RedSet := RSet Colour.red
  RedAtom := RSet Colour.black
  BlackSet := RSet Colour.black
  BlackAtom := RSet Colour.red
  redAtomsAsBlackSets := Equiv.refl (RSet Colour.black)
  blackAtomsAsRedSets := Equiv.refl (RSet Colour.red)
  redBlackSetSwap := redBlackSetEquiv
  redBlackAtomSwap := redBlackAtomEquiv

/-- In the rset instance, dropping a quoted red atom is definitionally the black set it sealed. -/
theorem reflective_dropRed_quoteRed (x : RSet Colour.black) :
    reflectiveUniverse.dropRed (reflectiveUniverse.quoteRed x) = x :=
  ReflectiveUniverse.dropRed_quoteRed reflectiveUniverse x

/-- In the rset instance, quoting a dropped red atom returns the same black finite set. -/
theorem reflective_quoteRed_dropRed (x : RSet Colour.black) :
    reflectiveUniverse.quoteRed (reflectiveUniverse.dropRed x) = x :=
  ReflectiveUniverse.quoteRed_dropRed reflectiveUniverse x

/-- In the rset instance, dropping a quoted black atom is definitionally the red set it sealed. -/
theorem reflective_dropBlack_quoteBlack (x : RSet Colour.red) :
    reflectiveUniverse.dropBlack (reflectiveUniverse.quoteBlack x) = x :=
  ReflectiveUniverse.dropBlack_quoteBlack reflectiveUniverse x

/-- In the rset instance, quoting a dropped black atom returns the same red finite set. -/
theorem reflective_quoteBlack_dropBlack (x : RSet Colour.red) :
    reflectiveUniverse.quoteBlack (reflectiveUniverse.dropBlack x) = x :=
  ReflectiveUniverse.quoteBlack_dropBlack reflectiveUniverse x

/-- The reflective-universe red-to-black set swap is the concrete rset colour swap. -/
theorem reflective_redBlackSetSwap (x : RSet Colour.red) :
    reflectiveUniverse.redBlackSetSwap x = redToBlackSet x :=
  rfl

/-- The reflective-universe black-to-red set swap is the inverse concrete rset colour swap. -/
theorem reflective_blackRedSetSwap (x : RSet Colour.black) :
    reflectiveUniverse.redBlackSetSwap.symm x = blackToRedSet x :=
  rfl

/-- The reflective-universe red-atom-to-black-atom swap is the concrete black-to-red set swap. -/
theorem reflective_redBlackAtomSwap (x : RSet Colour.black) :
    reflectiveUniverse.redBlackAtomSwap x = blackToRedSet x :=
  rfl

/-- The reflective-universe black-atom-to-red-atom swap is the concrete red-to-black set swap. -/
theorem reflective_blackRedAtomSwap (x : RSet Colour.red) :
    reflectiveUniverse.redBlackAtomSwap.symm x = redToBlackSet x :=
  rfl

end RSetModel
end MeTTaIL
