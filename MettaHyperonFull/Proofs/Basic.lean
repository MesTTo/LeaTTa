import Mathlib
import MettaHyperonFull

/-!
# Metatheory infrastructure

A structural induction principle for the nested inductive `Atom`, plus the structural lemmas
about variable renaming reused throughout the metatheory layer.

`induction a` does not work out of the box on `Atom`, because `Atom.expr : List Atom → Atom`
makes it a *nested* inductive. `Atom.recAux` supplies the missing principle: in the `expr`
case one may assume the motive for every immediate sub-atom, and is tagged
`@[induction_eliminator]` so that plain `induction a` uses it everywhere downstream.
-/

namespace Metta

namespace Atom

/-- Structural induction for the nested inductive `Atom`: to prove `motive a` for every `a`,
handle the four constructors, and in the `expr` case assume `motive` for each immediate
sub-atom. Tagged `@[induction_eliminator]`, so `induction a` uses it. Terminates because every
sub-atom is strictly smaller in `Atom.size` (`_ha : a ∈ xs` is used in `decreasing_by`). -/
-- `nolint defLemma`: although `motive`-valued, this is an *eliminator* (tagged
-- `induction_eliminator`), where being a `def`, not a `theorem`, is the intended form.
@[elab_as_elim, induction_eliminator, nolint defLemma]
def recAux {motive : Atom → Prop}
    (sym : ∀ s, motive (Atom.sym s))
    (var : ∀ v, motive (Atom.var v))
    (gnd : ∀ g, motive (Atom.gnd g))
    (expr : ∀ xs, (∀ a ∈ xs, motive a) → motive (Atom.expr xs)) :
    (a : Atom) → motive a
  | Atom.sym s => sym s
  | Atom.var v => var v
  | Atom.gnd g => gnd g
  | Atom.expr xs => expr xs (fun a _ha => recAux sym var gnd expr a)
  termination_by a => a.size
  decreasing_by
    simp only [Atom.size]
    have h : Atom.size a ≤ (xs.map Atom.size).sum :=
      List.single_le_sum (by intro _ _; exact Nat.zero_le _) _ (List.mem_map_of_mem _ha)
    omega

end Atom

/-- Renaming variables by the empty map is the identity. -/
theorem renameVars_nil (a : Atom) : renameVars [] a = a := by
  induction a with
  | expr xs ih => simp only [renameVars]; rw [List.map_congr_left ih]; simp
  | _ => simp [renameVars]

/-- Variable renaming preserves `Atom.size`: it replaces variables by variables, leaf-for-leaf. -/
theorem size_renameVars (m : List (VarName × VarName)) (a : Atom) :
    (renameVars m a).size = a.size := by
  induction a with
  | expr xs ih =>
      have hmap : (xs.map (renameVars m)).map Atom.size = xs.map Atom.size := by
        rw [List.map_map]; exact List.map_congr_left (fun a ha => ih a ha)
      simp only [renameVars, Atom.size, hmap]
  | _ => simp [renameVars, Atom.size]

end Metta
