import MettaHyperonFull.Proofs.Substitution

/-!
# Metatheory: subject reduction (type preservation) for user-defined rewriting

`Proofs/TypeSoundness.lean` proved preservation only for the *grounded* core; this file proves
**type preservation for MeTTa's user-defined `=`-rewriting**.

MeTTa has *no published type calculus or soundness theorem*. Both the Hyperon whitepaper and the
"Reflective Metagraph Rewriting" paper say the type system is the operational `get_atom_types` and
that a formal preservation result is future work. We reconstruct a **compositional typing
judgment** `WT`, a standalone declarative typing relation for MeTTa's user rewriting. It uses the
same `(: a T)` data source as `Core.HasType` but is independent of the kernel's operational
`getTypes`/`typeMismatch`; subject reduction is proved for this declarative discipline. The
judgment comprises a context `Γ` for rule variables, the space's `(: a T)` declarations, arrow
elimination for application (`WT.app`), and subtyping with a gradual top (`WT.sub`, since
`TypeEnv.inherits _ _ Atom` and `… %Undefined%` hold). The key step is the substitution lemma
(`WT.subst`): typing is stable under a substitution that grounds the variable context.

`reduction_preserves_type` follows directly. A MeTTa rewrite step fires a rule `(= L R)` by
matching a redex against `L`, binding `σ`, and rewriting to `σ R`, as in Hyperon's `interpret`.
If the rule is type-preserving (`L` and `R` share a type `T` under `Γ`), then for any grounding
`σ` both `σ L` and `σ R` have type `T`.

Assumption: the type-preserving-rule hypothesis is stated explicitly. MeTTa does not check
`type(L) = type(R)` when a rule is asserted (equality inference is deferred to the interpreter
loop), so the caller must supply this assumption. It is the formal analogue of "the programmer
wrote a well-typed rule."

## Scope

* **Fixed signature.** `Γ` and `env` are fixed across the step. MeTTa's reflection (programs
  rewriting their own `:`/`<:` facts) is out of scope. Preservation holds for the fragment that
  reduces against a settled signature.
* **Set-valued typing.** MeTTa's `get_atom_types` returns a *set* (no principal type); `WT _ _ a T`
  is "`T` is *one* of `a`'s types". Preservation is existential over that set, matching the
  operational reading.
* The gradual wildcards `%Undefined%` and `Atom` enter through `WT.sub`, since both are universal
  supertypes under `TypeEnv.inherits`.
-/

namespace Metta
open Metta

/-- `(-> A₁ … Aₙ R)` from argument types and return type; nullary `[]` is just `R`. -/
def mkArrow : List Atom → Atom → Atom
  | [], R => R
  | As@(_ :: _), R => Atom.expr (Atom.sym "->" :: (As ++ [R]))

mutual
/-- Compositional typing `Γ ⊢ a : T`: a context `Γ` for (rule) variables plus the space's
    `(: a T)` declarations, with the application rule (arrow elimination) and subtyping/gradual top.
    Standalone declarative judgment, independent of the kernel's `getTypes`, over which
    the substitution lemma and subject reduction are proved. -/
inductive WT (env : TypeEnv) : List (VarName × Atom) → Atom → Atom → Prop where
  /-- A rule variable has the type the context assigns it. -/
  | var  {Γ x T}          : (x, T) ∈ Γ → WT env Γ (Atom.var x) T
  /-- A *closed* atom declared `(: a T)` in the space has type `T`. -/
  | decl {Γ a T}          : a.vars = [] → (a, T) ∈ env.assignments → WT env Γ a T
  /-- **Application (arrow elimination).** If `f : (-> argTs… R)` and the arguments have the
      parameter types, then `(f args…) : R`. -/
  | app  {Γ f args argTs R} :
      WT env Γ f (mkArrow argTs R) → WTArgs env Γ args argTs →
      WT env Γ (Atom.expr (f :: args)) R
  /-- Subsumption: `a : t` and `t <: u` (which includes the gradual tops `Atom`/`%Undefined%`)
      give `a : u`. -/
  | sub  {Γ a t u}        : WT env Γ a t → TypeEnv.inherits env t u = true → WT env Γ a u
/-- Pointwise typing of an argument list against a parameter-type list (used by `WT.app`). -/
inductive WTArgs (env : TypeEnv) : List (VarName × Atom) → List Atom → List Atom → Prop where
  | nil  {Γ}                : WTArgs env Γ [] []
  | cons {Γ a rest A Rest}  : WT env Γ a A → WTArgs env Γ rest Rest →
                              WTArgs env Γ (a :: rest) (A :: Rest)
end

/-- A substitution `σ` **grounds** the variable context `Γ`: every variable's substitute has the
    type `Γ` assigns it (in the empty context). A rule-firing substitution satisfies `Grounds`
    when the matched redex is well-typed. -/
def Grounds (env : TypeEnv) (σ : Subst) (Γ : List (VarName × Atom)) : Prop :=
  ∀ x T, (x, T) ∈ Γ → WT env [] (Subst.apply σ (Atom.var x)) T

mutual
/-- **Substitution lemma.** Typing is stable under a substitution that grounds the context: if
    `Γ ⊢ a : T` and `σ` grounds `Γ`, then `⊢ σ(a) : T`. Proved by structural recursion on the typing
    derivation, mutually with `WTArgs.subst`. -/
theorem WT.subst {env : TypeEnv} {Γ : List (VarName × Atom)} {σ : Subst}
    (hσ : Grounds env σ Γ) : ∀ {a T : Atom}, WT env Γ a T → WT env [] (Subst.apply σ a) T
  | _, _, .var hm => hσ _ _ hm
  | _, _, .decl hc hmem => by rw [Subst.apply_of_closed σ _ hc]; exact WT.decl hc hmem
  | _, _, .app hf hargs => by
      simp only [Subst.apply, List.map_cons]
      exact WT.app (WT.subst hσ hf) (WTArgs.subst hσ hargs)
  | _, _, .sub ha hi => WT.sub (WT.subst hσ ha) hi
/-- Argument-list companion of `WT.subst`. -/
theorem WTArgs.subst {env : TypeEnv} {Γ : List (VarName × Atom)} {σ : Subst}
    (hσ : Grounds env σ Γ) :
    ∀ {args argTs : List Atom}, WTArgs env Γ args argTs →
      WTArgs env [] (args.map (Subst.apply σ)) argTs
  | _, _, .nil => WTArgs.nil
  | _, _, .cons ha hrest => WTArgs.cons (WT.subst hσ ha) (WTArgs.subst hσ hrest)
end

/-- **Subject reduction for user-defined rewriting.** A MeTTa rewrite step fires a rule `(= L R)`
    by matching a redex against `L` with substitution `σ` and rewriting to `σ R`. If the rule is
    **type-preserving** (`L` and `R` share a type `T` under `Γ`), then for every grounding `σ`,
    both `σ L` and `σ R` have type `T`.

    Combined with the grounded-core preservation in `TypeSoundness.lean` and the
    permissiveness/totality/faithful-error results there, `reduction_preserves_type` completes the
    preservation half of type soundness for the typed fragment. -/
theorem reduction_preserves_type {env : TypeEnv} {Γ : List (VarName × Atom)} {L R T : Atom}
    {σ : Subst} (hσ : Grounds env σ Γ) (hL : WT env Γ L T) (hR : WT env Γ R T) :
    WT env [] (Subst.apply σ L) T ∧ WT env [] (Subst.apply σ R) T :=
  ⟨WT.subst hσ hL, WT.subst hσ hR⟩

end Metta
