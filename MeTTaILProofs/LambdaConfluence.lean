/-
Confluence (Church-Rosser) of beta reduction for the simply-typed lambda calculus of
`MeTTaIL/Calculi/Lambda.lean`.

We reuse `Tm`, `shift`, `subst` and `Step` from `Lambda.lean` unchanged. The proof is the standard
Tait / Martin-Löf / Takahashi argument by parallel reduction.

* `ParRed` is one-step parallel reduction: it may contract any set of beta redexes at once, in
  particular none (so it is reflexive) or several in parallel. One `Step` is one `ParRed`, and one
  `ParRed` is a finite run of `Step`s, so the reflexive-transitive closures of `Step` and `ParRed`
  coincide.
* `Tm.dev a` is the complete development of `a`: contract every redex already in `a`, all at once.
  The triangle property `ParRed a b → ParRed b (Tm.dev a)` says `dev a` is the greatest parallel
  reduct, so it caps any parallel step out of `a`. The triangle gives the diamond for `ParRed` for
  free.
* The diamond for `ParRed` transfers to its closure, which equals the closure of `Step`, so
  `Relation.church_rosser` delivers confluence of `Step` (`confluence`).

The technical heart is the substitution lemma for `ParRed` (`par_subst`), and under it the de Bruijn
arithmetic relating `shift` and `subst`. Those identities mirror the index bookkeeping already done
in `Lambda.lean`'s `weakening` and `subst_hasTy`: each is an induction on the term, the binder cases
bump the cutoffs and indices by one, `omega` discharges the order side conditions, and the variable
case is the three-way split that `shift` and `subst` already perform.
-/
import MeTTaIL.Calculi.Lambda
import Mathlib.Logic.Relation
import Mathlib.Tactic.SplitIfs

namespace MeTTaIL.STLC

open Tm

/-!
### de Bruijn arithmetic for `shift` and `subst`

Five equalities about how `shift 1` and `subst` interact. We only ever need shift width `1`, because
the binder cases of `subst` always lift the substituend by exactly one.
-/

/-- Two shifts of width one commute, reindexing the cutoffs. -/
theorem shift_shift_exchange (t : Tm) :
    ∀ {c d : Nat}, c ≤ d → shift 1 c (shift 1 d t) = shift 1 (d + 1) (shift 1 c t) := by
  induction t with
  | var i =>
      intro c d hcd
      simp only [shift]
      split_ifs <;> simp only [shift] <;> split_ifs <;> first | rfl | (exfalso; omega)
  | lam ty body ih =>
      intro c d hcd
      simp only [shift]
      rw [ih (by omega : c + 1 ≤ d + 1)]
  | app fn arg ihf iha =>
      intro c d hcd
      simp only [shift]
      rw [ihf hcd, iha hcd]

/-- Pushing a width-one shift with cutoff `c` through a substitution at index `j ≥ c`: the shift
    skips the substituted slot, so the slot index moves up to `j+1` and the substituend is shifted
    to match. -/
theorem shift_subst_le (b : Tm) :
    ∀ {c j : Nat} {s : Tm}, c ≤ j → shift 1 c (b[j := s]) = (shift 1 c b)[j + 1 := shift 1 c s] := by
  induction b with
  | var i =>
      intro c j s hcj
      simp only [subst, shift]
      split_ifs <;> simp only [shift, subst] <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega)
  | lam ty body ih =>
      intro c j s hcj
      simp only [subst, shift]
      rw [ih (by omega : c + 1 ≤ j + 1)]
      rw [shift_shift_exchange s (Nat.zero_le c)]
  | app fn arg ihf iha =>
      intro c j s hcj
      simp only [subst, shift]
      rw [ihf hcj, iha hcj]

/-- Pushing a width-one shift with cutoff `c` through a substitution at index `j ≤ c`: the shift now
    lands above the slot, so the term is shifted at the raised cutoff `c+1` while the slot index
    stays `j` and the substituend is shifted at `c`. -/
theorem shift_subst_ge (b : Tm) :
    ∀ {c j : Nat} {s : Tm}, j ≤ c → shift 1 c (b[j := s]) = (shift 1 (c + 1) b)[j := shift 1 c s] := by
  induction b with
  | var i =>
      intro c j s hjc
      simp only [subst, shift]
      split_ifs <;> simp only [shift, subst] <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega)
  | lam ty body ih =>
      intro c j s hjc
      simp only [subst, shift]
      rw [ih (by omega : j + 1 ≤ c + 1)]
      rw [shift_shift_exchange s (Nat.zero_le c)]
  | app fn arg ihf iha =>
      intro c j s hjc
      simp only [subst, shift]
      rw [ihf hjc, iha hjc]

/-- Substituting at an index that a fresh shift just opened up cancels: `shift 1 j` makes index `j`
    free, then `[j := u]` removes it again, recovering the original term. -/
theorem subst_shift_cancel (t : Tm) :
    ∀ {j : Nat} {u : Tm}, (shift 1 j t)[j := u] = t := by
  induction t with
  | var i =>
      intro j u
      simp only [shift]
      split_ifs <;> simp only [subst] <;> split_ifs <;> first | rfl | (exfalso; omega)
  | lam ty body ih =>
      intro j u
      simp only [shift, subst]
      rw [ih]
  | app fn arg ihf iha =>
      intro j u
      simp only [shift, subst]
      rw [ihf, iha]

/-- The substitution-commutation lemma (Barendregt 2.1.16, de Bruijn form). For `i ≤ j`, doing the
    inner substitution at `i` then the outer at `j` equals doing the outer first (at the raised slot
    `j+1`, with its substituend shifted past `i`) and then the inner at `i` (with its substituend
    itself substituted). This is what makes the beta case of `par_subst` go through: it is the case
    `i = 0`. -/
theorem subst_subst (b : Tm) :
    ∀ {i j : Nat} {a s : Tm}, i ≤ j →
      (b[i := a])[j := s] = (b[j + 1 := shift 1 i s])[i := a[j := s]] := by
  induction b with
  | var k =>
      intro i j a s hij
      simp only [subst]
      split_ifs <;> simp only [subst, subst_shift_cancel] <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega)
  | lam ty body ih =>
      intro i j a s hij
      simp only [subst]
      rw [ih (by omega : i + 1 ≤ j + 1)]
      rw [shift_shift_exchange s (Nat.zero_le i)]
      rw [shift_subst_le a (Nat.zero_le j)]
  | app fn arg ihf iha =>
      intro i j a s hij
      simp only [subst]
      rw [ihf hij, iha hij]

/-!
### Parallel reduction

`ParRed` contracts any number of beta redexes simultaneously, including zero. The first three rules
are the reflexive/congruence closure; the last fires a beta redex while reducing both halves in
parallel. Reflexivity (`ParRed.refl`) and the fact that one `Step` is one `ParRed` follow at once.
-/

/-- Parallel (Takahashi) reduction: contract any set of redexes already present, all at once. -/
inductive ParRed : Tm → Tm → Prop where
  | var (i : Nat) : ParRed (.var i) (.var i)
  | lam {ty b b'} : ParRed b b' → ParRed (.lam ty b) (.lam ty b')
  | app {f f' a a'} : ParRed f f' → ParRed a a' → ParRed (.app f a) (.app f' a')
  | beta {ty b b' s s'} : ParRed b b' → ParRed s s' →
      ParRed (.app (.lam ty b) s) (b'[0 := s'])

/-- Parallel reduction is reflexive: every term reduces to itself by contracting nothing. -/
theorem ParRed.refl : ∀ t : Tm, ParRed t t
  | .var i => .var i
  | .lam _ty b => .lam (ParRed.refl b)
  | .app f a => .app (ParRed.refl f) (ParRed.refl a)

/-- Parallel reduction commutes with a width-one shift: shifting both sides at any cutoff `c`
    preserves the parallel step. The beta case uses `shift_subst_ge` to push the shift through the
    contracted substitution. -/
theorem par_shift {t t' : Tm} (h : ParRed t t') : ∀ c : Nat, ParRed (shift 1 c t) (shift 1 c t') := by
  induction h with
  | var i =>
      intro c
      simp only [shift]
      split_ifs <;> exact ParRed.var _
  | lam _ ih =>
      intro c
      simp only [shift]
      exact .lam (ih (c + 1))
  | app _ _ ihf iha =>
      intro c
      simp only [shift]
      exact .app (ihf c) (iha c)
  | @beta ty b b' s s' _ _ ihb ihs =>
      intro c
      simp only [shift]
      rw [shift_subst_ge b' (Nat.zero_le c)]
      exact .beta (ihb (c + 1)) (ihs c)

/-- The substitution lemma for parallel reduction: parallel steps are stable under substituting a
    parallel-reducing term for a variable. The induction is on the derivation for `t`, generalizing
    the index `j` and both substituends `s, s'` (these change under a binder, where the substituend
    is shifted). The lam case shifts the substituends with `par_shift`; the beta case rewrites the
    nested substitution with `subst_subst` (its `i = 0` instance). -/
theorem par_subst {t t' : Tm} (ht : ParRed t t') :
    ∀ {s s' : Tm}, ParRed s s' → ∀ j : Nat, ParRed (t[j := s]) (t'[j := s']) := by
  induction ht with
  | var i =>
      intro s s' hs j
      simp only [subst]
      split_ifs
      · exact ParRed.var _
      · exact hs
      · exact ParRed.var _
  | lam _ ih =>
      intro s s' hs j
      simp only [subst]
      exact .lam (ih (par_shift hs 0) (j + 1))
  | app _ _ ihf iha =>
      intro s s' hs j
      simp only [subst]
      exact .app (ihf hs j) (iha hs j)
  | @beta ty b b' u u' _ _ ihb ihu =>
      intro s s' hs j
      simp only [subst]
      rw [subst_subst b' (Nat.zero_le j)]
      exact .beta (ihb (par_shift hs 0) (j + 1)) (ihu hs j)

/-!
### Complete development and the triangle property

`Tm.dev a` is the complete development of `a`: contract every redex already present in `a`,
simultaneously. The triangle property says `dev a` is the greatest one-step parallel reduct of `a`:
if `ParRed a b`, then `ParRed b (dev a)`. The triangle gives the diamond for `ParRed` directly,
without any further case analysis.
-/

/-- The complete development: fire every redex currently in the term, all at once. The only
    interesting clause is an application whose function is a `lam`: that is a redex, so it is
    contracted, developing both halves first. -/
def Tm.dev : Tm → Tm
  | .var i => .var i
  | .lam ty b => .lam ty (Tm.dev b)
  | .app (.lam _ b) a => (Tm.dev b)[0 := Tm.dev a]
  | .app (.var i) a => .app (.var i) (Tm.dev a)
  | .app (.app f g) a => .app (Tm.dev (.app f g)) (Tm.dev a)

/-- Inversion for a parallel step out of a `lam`: it can only be a `lam` congruence. -/
theorem ParRed.lam_inv {ty : Ty} {b g : Tm} (h : ParRed (.lam ty b) g) :
    ∃ b', g = .lam ty b' ∧ ParRed b b' := by
  cases h with
  | lam hb => exact ⟨_, rfl, hb⟩

/-- Triangle property: `dev a` is the maximal parallel reduct, so every parallel step `a ⇉ b` is
    capped by `b ⇉ dev a`. Induction on the derivation, casing in the application rule on whether the
    function is a `lam` (then the application is itself a redex that `dev` contracts). -/
theorem par_triangle {a b : Tm} (h : ParRed a b) : ParRed b (Tm.dev a) := by
  induction h with
  | var i => exact ParRed.var i
  | lam _ ih => exact .lam ih
  | @app f f' a a' hf _ ihf iha =>
      cases f with
      | var i =>
          cases hf with
          | var => exact .app ihf iha
      | lam ty c =>
          -- `f = lam ty c`, so `app f a` is a redex; `dev` contracts it to `(dev c)[0 := dev a]`.
          obtain ⟨c', rfl, _⟩ := ParRed.lam_inv hf
          -- `ihf : ParRed (lam ty c') (dev (lam ty c))` and `dev (lam ty c) = lam ty (dev c)`.
          have ihf' : ParRed (Tm.lam ty c') (.lam ty (Tm.dev c)) := by simpa only [Tm.dev] using ihf
          cases ihf' with
          | lam hc' =>
              -- now `app (lam ty c') a'` beta-reduces to `(dev c)[0 := dev a]`.
              simp only [Tm.dev]
              exact .beta hc' iha
      | app g h =>
          exact .app ihf iha
  | @beta ty b b' s s' _ _ ihb ihs =>
      simp only [Tm.dev]
      exact par_subst ihb ihs 0

/-- The diamond property for parallel reduction, read straight off the triangle: both reducts of `a`
    are capped by the single term `dev a`. -/
theorem par_diamond {a b c : Tm} (hb : ParRed a b) (hc : ParRed a c) :
    ∃ d, ParRed b d ∧ ParRed c d :=
  ⟨Tm.dev a, par_triangle hb, par_triangle hc⟩

/-!
### Transfer to single-step reduction

One `Step` is one `ParRed`, and one `ParRed` is a finite sequence of `Step`s, so the
reflexive-transitive closures of the two relations coincide. The diamond for `ParRed` then gives
confluence for `Step` through `Relation.church_rosser`.
-/

open Relation

/-- Reduction under `lam` lifts to the reflexive-transitive closure. -/
theorem reflTransGen_step_lam {ty : Ty} {b b' : Tm} (h : ReflTransGen Step b b') :
    ReflTransGen Step (.lam ty b) (.lam ty b') :=
  ReflTransGen.lift (Tm.lam ty) (fun _ _ hs => Step.lam hs) h

/-- Reduction on the left of an application lifts to the closure. -/
theorem reflTransGen_step_appL {f f' a : Tm} (h : ReflTransGen Step f f') :
    ReflTransGen Step (.app f a) (.app f' a) :=
  ReflTransGen.lift (fun x => Tm.app x a) (fun _ _ hs => Step.appL hs) h

/-- Reduction on the right of an application lifts to the closure. -/
theorem reflTransGen_step_appR {f a a' : Tm} (h : ReflTransGen Step a a') :
    ReflTransGen Step (.app f a) (.app f a') :=
  ReflTransGen.lift (fun x => Tm.app f x) (fun _ _ hs => Step.appR hs) h

/-- Reduction on both sides of an application lifts to the closure, by composing the two one-sided
    lifts. -/
theorem reflTransGen_step_app {f f' a a' : Tm}
    (hf : ReflTransGen Step f f') (ha : ReflTransGen Step a a') :
    ReflTransGen Step (.app f a) (.app f' a') :=
  (reflTransGen_step_appL hf).trans (reflTransGen_step_appR ha)

/-- Every single beta step is a parallel step (contracting exactly one redex). -/
theorem step_to_par {a b : Tm} (h : Step a b) : ParRed a b := by
  induction h with
  | beta => exact .beta (ParRed.refl _) (ParRed.refl _)
  | appL _ ih => exact .app ih (ParRed.refl _)
  | appR _ ih => exact .app (ParRed.refl _) ih
  | lam _ ih => exact .lam ih

/-- Every parallel step is a finite sequence of beta steps. The beta case reduces the function and
    argument first (using the congruence lifts), then fires the redex with `Step.beta`. -/
theorem par_to_redstep {a b : Tm} (h : ParRed a b) : ReflTransGen Step a b := by
  induction h with
  | var i => exact .refl
  | lam _ ih => exact reflTransGen_step_lam ih
  | app _ _ ihf iha => exact reflTransGen_step_app ihf iha
  | @beta ty b b' s s' _ _ ihb ihs =>
      -- `app (lam ty b) s ↠ app (lam ty b') s' →β b'[0 := s']`
      refine (reflTransGen_step_app (reflTransGen_step_lam ihb) ihs).trans ?_
      exact ReflTransGen.single Step.beta

/-- The reflexive-transitive closures of `Step` and `ParRed` agree. -/
theorem reflTransGen_step_eq_par : ReflTransGen Step = ReflTransGen ParRed := by
  funext a b
  apply propext
  constructor
  · exact fun h => h.mono (fun _ _ => step_to_par)
  · exact fun h => reflTransGen_closed (fun _ _ => par_to_redstep) h

/-- **Confluence (Church-Rosser) of beta reduction** for the simply-typed lambda calculus. If a term
    `a` reduces (in any number of steps) to both `b` and `c`, the two reducts can be brought back
    together: there is a common `d` reachable from each. The proof routes through parallel reduction:
    `ParRed` has the diamond property (`par_diamond`, from the complete development), its closure
    equals that of `Step`, and `Relation.church_rosser` lifts the diamond to confluence. -/
theorem confluence {a b c : Tm} :
    ReflTransGen Step a b → ReflTransGen Step a c →
    ∃ d, ReflTransGen Step b d ∧ ReflTransGen Step c d := by
  intro hab hac
  rw [reflTransGen_step_eq_par] at hab hac
  have hcr : Join (ReflTransGen ParRed) b c :=
    church_rosser
      (fun _ _ _ hb hc =>
        let ⟨d, hbd, hcd⟩ := par_diamond hb hc
        ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩)
      hab hac
  obtain ⟨d, hbd, hcd⟩ := hcr
  rw [← reflTransGen_step_eq_par] at hbd hcd
  exact ⟨d, hbd, hcd⟩

end MeTTaIL.STLC
