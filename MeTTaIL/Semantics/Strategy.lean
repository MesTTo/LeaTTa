/-
Module: MeTTaIL.Semantics.Strategy
Layer: Semantics
Purpose: Evaluation-context strategies, the K-framework style of strictness. A strategy says, for each
  operator and argument position, whether the reducer may descend there. `oneStepStrat` is the
  leftmost-outermost reducer restricted to the strategy's positions: it tries a base rewrite at the root,
  then descends only into the strategy-allowed argument positions (left to right), and into the Subst
  components. Restricting where the reducer looks only prunes the search, so soundness is inherited:
  `oneStepStrat_sound` shows every step it takes is a genuine `RewStep`. The all-positions strategy
  recovers the unrestricted reducer (`oneStepStrat_all`), so this is a faithful generalization of
  `oneStep`.
Imports: MeTTaIL.Semantics.Context
Trusted boundary: none (fully proved)
Main exports: Strategy, oneStepStrat, oneStepStratList, oneStepStrat_sound, oneStepStratList_sound,
  oneStepStrat_all
Open obligations: none
-/
import MeTTaIL.Semantics.Context

namespace MeTTaIL

/-- An evaluation strategy: for an operator `l` and argument index `i`, may the reducer descend into
    that position? K-style strictness annotations are exactly such a predicate (strict in position `i`
    means the strategy allows descending there). -/
abbrev Strategy := Label → Nat → Bool

mutual
  /-- The leftmost-outermost reducer restricted to a strategy: try a base rewrite at the root, else
      descend into the strategy-allowed argument positions (left to right), then the Subst components. -/
  def oneStepStrat (s : Strategy) (p : Presentation) : AST → Option AST
    | .var x =>
        match baseReducts p (.var x) with
        | r :: _ => some r
        | [] => none
    | .sexp l args =>
        match baseReducts p (.sexp l args) with
        | r :: _ => some r
        | [] => (oneStepStratList s p l 0 args).map (fun args' => AST.sexp l args')
    | .subst b r v =>
        match baseReducts p (.subst b r v) with
        | u :: _ => some u
        | [] =>
            match oneStepStrat s p b with
            | some b' => some (.subst b' r v)
            | none => (oneStepStrat s p r).map (fun r' => AST.subst b r' v)
  /-- Step inside the first strategy-allowed reducible argument. `l` is the operator and `i` indexes the
      head of the remaining argument list, so positions are counted from the original left edge. -/
  def oneStepStratList (s : Strategy) (p : Presentation) (l : Label) :
      Nat → List AST → Option (List AST)
    | _, [] => none
    | i, a :: as =>
        if s l i then
          match oneStepStrat s p a with
          | some a' => some (a' :: as)
          | none => (oneStepStratList s p l (i + 1) as).map (fun as' => a :: as')
        else (oneStepStratList s p l (i + 1) as).map (fun as' => a :: as')
end

mutual
  /-- Soundness: every strategy-restricted one-step reduct is a genuine context rewrite. Pruning the
      search positions cannot create a spurious step. -/
  theorem oneStepStrat_sound (s : Strategy) (p : Presentation) :
      ∀ (t : AST) {t' : AST}, oneStepStrat s p t = some t' → RewStep p t t'
    | .var x, t', h => by
        simp only [oneStepStrat] at h
        split at h
        · rename_i r _ heq
          cases h
          exact RewStep.top (reduces_of_mem_baseReducts (by rw [heq]; exact List.mem_cons_self ..))
        · exact absurd h (by simp)
    | .sexp l args, t', h => by
        simp only [oneStepStrat] at h
        split at h
        · rename_i r _ heq
          cases h
          exact RewStep.top (reduces_of_mem_baseReducts (by rw [heq]; exact List.mem_cons_self ..))
        · rename_i _
          rcases hopt : oneStepStratList s p l 0 args with _ | args'
          · rw [hopt] at h; simp at h
          · rw [hopt] at h; simp only [Option.map_some] at h
            cases h
            obtain ⟨pre, a, a', post, hargs, hargs', hstep⟩ := oneStepStratList_sound s p l 0 args hopt
            subst hargs; subst hargs'
            exact RewStep.arg hstep
    | .subst b r v, t', h => by
        simp only [oneStepStrat] at h
        split at h
        · rename_i u _ heq
          cases h
          exact RewStep.top (reduces_of_mem_baseReducts (by rw [heq]; exact List.mem_cons_self ..))
        · rename_i _
          split at h
          · rename_i b' hb
            cases h
            exact RewStep.substB (oneStepStrat_sound s p b hb)
          · rename_i hb
            rcases hopt : oneStepStrat s p r with _ | r'
            · rw [hopt] at h; simp at h
            · rw [hopt] at h; simp only [Option.map_some] at h
              cases h
              exact RewStep.substR (oneStepStrat_sound s p r hopt)
  /-- Soundness for the list reducer: the result reduces exactly one argument in place, at a
      strategy-allowed position. -/
  theorem oneStepStratList_sound (s : Strategy) (p : Presentation) (l : Label) :
      ∀ (i : Nat) (args : List AST) {args' : List AST}, oneStepStratList s p l i args = some args' →
        ∃ (pre : List AST) (a a' : AST) (post : List AST),
          args = pre ++ a :: post ∧ args' = pre ++ a' :: post ∧ RewStep p a a'
    | _, [], args', h => by simp [oneStepStratList] at h
    | i, a :: as, args', h => by
        -- Both the strategy-skipped position and the unproductive-step position recurse into the tail in
        -- the same way; this handles that shared case once.
        have tail : ∀ {r : List AST},
            (oneStepStratList s p l (i + 1) as).map (fun as' => a :: as') = some r →
            ∃ (pre : List AST) (b b' : AST) (post : List AST),
              a :: as = pre ++ b :: post ∧ r = pre ++ b' :: post ∧ RewStep p b b' := by
          intro r hr
          rcases hopt : oneStepStratList s p l (i + 1) as with _ | as'
          · rw [hopt] at hr; simp at hr
          · rw [hopt] at hr; simp only [Option.map_some] at hr
            cases hr
            obtain ⟨pre, b, b', post, hpre, hpost, hstep⟩ :=
              oneStepStratList_sound s p l (i + 1) as hopt
            subst hpre; subst hpost
            exact ⟨a :: pre, b, b', post, rfl, rfl, hstep⟩
        simp only [oneStepStratList] at h
        split at h
        · split at h
          · rename_i a' ha
            cases h
            exact ⟨[], a, a', as, rfl, rfl, oneStepStrat_sound s p a ha⟩
          · exact tail h
        · exact tail h
end

mutual
  /-- The all-positions strategy recovers the unrestricted reducer: `oneStepStrat` then agrees with
      `oneStep`, so the strategy mechanism is a faithful generalization. -/
  theorem oneStepStrat_all (p : Presentation) :
      ∀ (t : AST), oneStepStrat (fun _ _ => true) p t = oneStep p t
    | .var _ => rfl
    | .sexp l args => by
        simp only [oneStepStrat, oneStep, oneStepStratList_all]
        cases baseReducts p (.sexp l args) <;> rfl
    | .subst b r v => by
        simp only [oneStepStrat, oneStep, oneStepStrat_all p b, oneStepStrat_all p r]
        cases baseReducts p (.subst b r v) <;> first | rfl | (cases oneStep p b <;> rfl)
  /-- List version of the agreement. The operator and index arguments do not matter when every position
      is allowed. -/
  theorem oneStepStratList_all (p : Presentation) (l : Label) :
      ∀ (i : Nat) (args : List AST), oneStepStratList (fun _ _ => true) p l i args = oneStepList p args
    | _, [] => rfl
    | i, a :: as => by
        simp only [oneStepStratList, oneStepList, if_true, oneStepStrat_all p a,
          oneStepStratList_all p l (i + 1) as]
        cases oneStep p a <;> rfl
end

end MeTTaIL
