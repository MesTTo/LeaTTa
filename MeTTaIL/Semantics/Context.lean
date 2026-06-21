/-
Module: MeTTaIL.Semantics.Context
Layer: Semantics
Purpose: The one-step rewrite relation closed under context, the standard reduction relation of the
  presentation's rewrite system, together with an executable one-step reducer. `RewStep` closes the
  existing top-level `Reduces` under `sexp`-argument and `Subst` contexts. `oneStep` searches
  leftmost-outermost for a redex: it tries a base rewrite at the root, and if none applies it descends
  left to right into the arguments, then into the `Subst` components. The headline is `oneStep_sound`:
  every step the executable reducer takes is a genuine `RewStep`, which reuses the matcher soundness
  `reduces_of_applyBaseRewrite`. Strategy note: leftmost-outermost is sound always, and by O'Donnell's
  theorem it is normalizing for left-normal orthogonal systems such as combinatory logic; finding a
  normal form for a general system needs parallel-outermost, which is future work.
Imports: MeTTaIL.Semantics.Relation
Trusted boundary: none (fully proved)
Main exports: RewStep, oneStep, oneStepList, reduces_of_mem_baseReducts, oneStep_sound,
  oneStepList_sound
Open obligations: completeness (that `oneStep` finds a redex whenever one exists) holds for left-normal
  orthogonal systems; the general normalizing strategy (parallel-outermost) is future work.
-/
import MeTTaIL.Semantics.Relation

namespace MeTTaIL

/-- One-step rewriting closed under context, the standard reduction relation of the presentation's
    rewrite system. The `top` rule embeds the existing top-level `Reduces`; the other rules let a step
    happen inside a `sexp` argument or a `Subst` component. -/
inductive RewStep (p : Presentation) : AST → AST → Prop where
  | top {t t' : AST} : Reduces p t t' → RewStep p t t'
  | arg {l : Label} {pre post : List AST} {a a' : AST} :
      RewStep p a a' → RewStep p (.sexp l (pre ++ a :: post)) (.sexp l (pre ++ a' :: post))
  | substB {b b' r : AST} {v : DottedPath} :
      RewStep p b b' → RewStep p (.subst b r v) (.subst b' r v)
  | substR {b r r' : AST} {v : DottedPath} :
      RewStep p r r' → RewStep p (.subst b r v) (.subst b r' v)

/-- Every member of `baseReducts` is a genuine top-level reduction. -/
theorem reduces_of_mem_baseReducts {p : Presentation} {t t' : AST}
    (h : t' ∈ baseReducts p t) : Reduces p t t' := by
  simp only [baseReducts, List.mem_filterMap] at h
  obtain ⟨rd, hmem, happly⟩ := h
  exact reduces_of_applyBaseRewrite p rd t t' hmem happly

mutual
  /-- One leftmost-outermost rewrite step, or `none` if the term is in normal form. Try a base rewrite
      at the root; if none applies, descend left to right into the arguments, then into the `Subst`
      components. -/
  def oneStep (p : Presentation) : AST → Option AST
    | .var x =>
        match baseReducts p (.var x) with
        | r :: _ => some r
        | [] => none
    | .sexp l args =>
        match baseReducts p (.sexp l args) with
        | r :: _ => some r
        | [] => (oneStepList p args).map (fun args' => AST.sexp l args')
    | .subst b r v =>
        match baseReducts p (.subst b r v) with
        | s :: _ => some s
        | [] =>
            match oneStep p b with
            | some b' => some (.subst b' r v)
            | none => (oneStep p r).map (fun r' => AST.subst b r' v)
  /-- One step inside the first reducible element of a list, or `none` if all are in normal form. -/
  def oneStepList (p : Presentation) : List AST → Option (List AST)
    | [] => none
    | a :: as =>
        match oneStep p a with
        | some a' => some (a' :: as)
        | none => (oneStepList p as).map (fun as' => a :: as')
end

mutual
  /-- Soundness: every executable one-step reduct is a genuine context rewrite. -/
  theorem oneStep_sound (p : Presentation) :
      ∀ (t : AST) {t' : AST}, oneStep p t = some t' → RewStep p t t'
    | .var x, t', h => by
        simp only [oneStep] at h
        split at h
        · rename_i r _ heq
          cases h
          exact RewStep.top (reduces_of_mem_baseReducts (by rw [heq]; exact List.mem_cons_self ..))
        · exact absurd h (by simp)
    | .sexp l args, t', h => by
        simp only [oneStep] at h
        split at h
        · rename_i r _ heq
          cases h
          exact RewStep.top (reduces_of_mem_baseReducts (by rw [heq]; exact List.mem_cons_self ..))
        · rename_i _
          rcases hopt : oneStepList p args with _ | args'
          · rw [hopt] at h; simp at h
          · rw [hopt] at h; simp only [Option.map_some] at h
            cases h
            obtain ⟨pre, a, a', post, hargs, hargs', hstep⟩ := oneStepList_sound p args hopt
            subst hargs; subst hargs'
            exact RewStep.arg hstep
    | .subst b r v, t', h => by
        simp only [oneStep] at h
        split at h
        · rename_i s _ heq
          cases h
          exact RewStep.top (reduces_of_mem_baseReducts (by rw [heq]; exact List.mem_cons_self ..))
        · rename_i _
          split at h
          · rename_i b' hb
            cases h
            exact RewStep.substB (oneStep_sound p b hb)
          · rename_i hb
            rcases hopt : oneStep p r with _ | r'
            · rw [hopt] at h; simp at h
            · rw [hopt] at h; simp only [Option.map_some] at h
              cases h
              exact RewStep.substR (oneStep_sound p r hopt)
  /-- Soundness for the list reducer: the result reduces exactly one element in place. -/
  theorem oneStepList_sound (p : Presentation) :
      ∀ (args : List AST) {args' : List AST}, oneStepList p args = some args' →
        ∃ (pre : List AST) (a a' : AST) (post : List AST),
          args = pre ++ a :: post ∧ args' = pre ++ a' :: post ∧ RewStep p a a'
    | [], args', h => by simp [oneStepList] at h
    | a :: as, args', h => by
        simp only [oneStepList] at h
        split at h
        · rename_i a' ha
          cases h
          exact ⟨[], a, a', as, rfl, rfl, oneStep_sound p a ha⟩
        · rename_i ha
          rcases hopt : oneStepList p as with _ | as'
          · rw [hopt] at h; simp at h
          · rw [hopt] at h; simp only [Option.map_some] at h
            cases h
            obtain ⟨pre, b, b', post, hpre, hpost, hstep⟩ := oneStepList_sound p as hopt
            subst hpre; subst hpost
            exact ⟨a :: pre, b, b', post, rfl, rfl, hstep⟩
end

end MeTTaIL
