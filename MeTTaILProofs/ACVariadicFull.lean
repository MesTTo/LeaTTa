/-
Module: MeTTaILProofs.ACVariadicFull
Layer: Proofs
Purpose: Full associative-commutative variadic operators, completing the `n`-ary AC obligation. Where
  `MeTTaILProofs.ACVariadic` handles commutativity (sorting the argument list), this adds associativity:
  a nested same-label node is flattened up into its parent, `(l a (l b c) d) = (l a b c d)`. The canonical
  form `canonAC` canonicalizes the arguments, flattens any argument that is a same-label node, and sorts
  the result by the verified total order. `ACEqAC` is the full variadic AC congruence (permuting and
  flattening the argument list of a flagged operator, closed under contexts), and `acEqAC_iff_canonAC` is
  the decision procedure. The flatten-soundness step composes via the prefix congruence `appendCong`, a
  natural admissible congruence for variadic operators (prepending a fixed prefix preserves equivalence),
  matching how AC normalization by flattening and sorting is justified in the rewriting literature.
Imports: MeTTaILProofs.AC (sortMS and its permutation/sortedness lemmas, the LinearOrder)
Trusted boundary: none (fully proved)
Main exports: ACEqAC, canonAC, canonAC_sound, canonAC_complete, acEqAC_iff_canonAC, instDecidableACEqAC
Open obligations: none for variadic AC; together with ACVariadic and AC this covers commutative and full
  AC for both binary-curried and n-ary operators.
-/
import MeTTaILProofs.AC

namespace MeTTaIL.AC

open List

/-- Pull up one same-label node: a flagged node `(l ...)` contributes its arguments, anything else is a
    single leaf. -/
def flatV (l : Label) (a : AST) : List AST :=
  match a with
  | .sexp m args => if l = m then args else [.sexp m args]
  | _ => [a]

/-- Full variadic AC equivalence: permute and flatten the argument list of a flagged `n`-ary operator. -/
inductive ACEqAC (acOp : Label → Bool) : AST → AST → Prop where
  | refl (t : AST) : ACEqAC acOp t t
  | symm {s t : AST} : ACEqAC acOp s t → ACEqAC acOp t s
  | trans {s t u : AST} : ACEqAC acOp s t → ACEqAC acOp t u → ACEqAC acOp s u
  | permC {l : Label} {args args' : List AST} :
      acOp l = true → args ~ args' → ACEqAC acOp (.sexp l args) (.sexp l args')
  | flatten {l : Label} (pre : List AST) {inner : List AST} (post : List AST) :
      acOp l = true →
      ACEqAC acOp (.sexp l (pre ++ .sexp l inner :: post)) (.sexp l (pre ++ inner ++ post))
  | appendCong {l : Label} (pre : List AST) {ys ys' : List AST} :
      ACEqAC acOp (.sexp l ys) (.sexp l ys') → ACEqAC acOp (.sexp l (pre ++ ys)) (.sexp l (pre ++ ys'))
  | argCong {l : Label} (pre : List AST) {a a' : AST} (post : List AST) :
      ACEqAC acOp a a' → ACEqAC acOp (.sexp l (pre ++ a :: post)) (.sexp l (pre ++ a' :: post))
  | substCongB {b b' r : AST} {v : DottedPath} :
      ACEqAC acOp b b' → ACEqAC acOp (.subst b r v) (.subst b' r v)
  | substCongR {b r r' : AST} {v : DottedPath} :
      ACEqAC acOp r r' → ACEqAC acOp (.subst b r v) (.subst b r' v)

variable (acOp : Label → Bool)

/-- Congruence of `sexp` under a pointwise `ACEqAC` of arguments. -/
lemma ACEqAC.sexpCongr {l : Label} {cs ds : List AST}
    (h : List.Forall₂ (ACEqAC acOp) cs ds) : ACEqAC acOp (.sexp l cs) (.sexp l ds) := by
  suffices H : ∀ (pre : List AST) {cs ds : List AST}, List.Forall₂ (ACEqAC acOp) cs ds →
      ACEqAC acOp (.sexp l (pre ++ cs)) (.sexp l (pre ++ ds)) by
    simpa using H [] h
  intro pre cs ds h
  induction h generalizing pre with
  | nil => exact ACEqAC.refl _
  | @cons c d cs' ds' hcd _ ih =>
      have step1 : ACEqAC acOp (.sexp l (pre ++ c :: cs')) (.sexp l (pre ++ d :: cs')) :=
        ACEqAC.argCong (l := l) pre cs' hcd
      have step2 : ACEqAC acOp (.sexp l (pre ++ d :: cs')) (.sexp l (pre ++ d :: ds')) := by
        have := ih (pre ++ [d]); simpa using this
      exact step1.trans step2

mutual
  /-- The full variadic AC canonical form: canonicalize arguments, flatten same-label children, sort. -/
  def canonAC : AST → AST
    | .var p => .var p
    | .subst b r v => .subst (canonAC b) (canonAC r) v
    | .sexp l args =>
        let cargs := canonACList args
        if acOp l then .sexp l (sortMS (cargs.flatMap (flatV l))) else .sexp l cargs
  def canonACList : List AST → List AST
    | [] => []
    | a :: as => canonAC a :: canonACList as
end

lemma canonACList_eq_map (ts : List AST) : canonACList acOp ts = ts.map (canonAC acOp) := by
  induction ts with
  | nil => rfl
  | cons a as ih => simp only [canonACList, ih, List.map_cons]

@[simp] lemma canonAC_var (p : DottedPath) : canonAC acOp (.var p) = .var p := rfl

@[simp] lemma canonAC_subst (b r : AST) (v : DottedPath) :
    canonAC acOp (.subst b r v) = .subst (canonAC acOp b) (canonAC acOp r) v := rfl

lemma canonAC_node {l : Label} (hac : acOp l = true) (args : List AST) :
    canonAC acOp (.sexp l args) = .sexp l (sortMS ((canonACList acOp args).flatMap (flatV l))) := by
  show (if acOp l then _ else _) = _
  rw [if_pos hac]

lemma canonAC_node_neg {l : Label} (hac : ¬ acOp l = true) (args : List AST) :
    canonAC acOp (.sexp l args) = .sexp l (canonACList acOp args) := by
  show (if acOp l then _ else _) = _
  rw [if_neg hac]

/-! ## Soundness -/

/-- Flattening the arguments of a flagged node is AC-equivalent to the node itself. Each same-label child
    pulled up is one `flatten` step; the prefix is carried by `appendCong`. -/
lemma flatMap_flatV_sound {l : Label} (hac : acOp l = true) :
    ∀ cargs : List AST, ACEqAC acOp (.sexp l (cargs.flatMap (flatV l))) (.sexp l cargs)
  | [] => ACEqAC.refl _
  | a :: as => by
      rw [List.flatMap_cons]
      have hi : ACEqAC acOp (.sexp l (flatV l a ++ as.flatMap (flatV l)))
          (.sexp l (flatV l a ++ as)) :=
        ACEqAC.appendCong (flatV l a) (flatMap_flatV_sound hac as)
      have hii : ACEqAC acOp (.sexp l (flatV l a ++ as)) (.sexp l (a :: as)) := by
        unfold flatV
        cases a with
        | sexp m args =>
            by_cases hlm : l = m
            · subst hlm
              simpa using (ACEqAC.flatten (l := l) [] as hac).symm
            · simp only [if_neg hlm]; exact ACEqAC.refl _
        | var x => exact ACEqAC.refl _
        | subst b r v => exact ACEqAC.refl _
      exact hi.trans hii

mutual
  theorem canonAC_sound : (t : AST) → ACEqAC acOp (canonAC acOp t) t
    | .var _ => ACEqAC.refl _
    | .subst b r v =>
        (ACEqAC.substCongB (canonAC_sound b)).trans (ACEqAC.substCongR (canonAC_sound r))
    | .sexp l args => by
        by_cases hac : acOp l
        · rw [canonAC_node acOp hac]
          have h1 : ACEqAC acOp (.sexp l (sortMS ((canonACList acOp args).flatMap (flatV l))))
              (.sexp l ((canonACList acOp args).flatMap (flatV l))) :=
            ACEqAC.permC hac (sortMS_perm _)
          have h2 := flatMap_flatV_sound acOp hac (canonACList acOp args)
          have h3 : ACEqAC acOp (.sexp l (canonACList acOp args)) (.sexp l args) :=
            ACEqAC.sexpCongr acOp (canonACList_sound args)
          exact (h1.trans h2).trans h3
        · rw [canonAC_node_neg acOp hac]
          exact ACEqAC.sexpCongr acOp (canonACList_sound args)
  theorem canonACList_sound : (ts : List AST) → List.Forall₂ (ACEqAC acOp) (canonACList acOp ts) ts
    | [] => List.Forall₂.nil
    | a :: as => List.Forall₂.cons (canonAC_sound a) (canonACList_sound as)
end

/-! ## Completeness -/

/-- Lists with equal sorts are permutations of each other. -/
lemma perm_of_sortMS_eq {A B : List AST} (h : sortMS A = sortMS B) : A ~ B :=
  ((sortMS_perm A).symm.trans (h ▸ sortMS_perm B))

theorem canonAC_complete {s t : AST} (h : ACEqAC acOp s t) : canonAC acOp s = canonAC acOp t := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @permC l args args' hac hperm =>
      rw [canonAC_node acOp hac, canonAC_node acOp hac, canonACList_eq_map, canonACList_eq_map]
      exact congrArg _ (sortMS_perm_eq ((hperm.map (canonAC acOp)).flatMap_right (flatV l)))
  | @flatten l pre inner post hac =>
      rw [canonAC_node acOp hac, canonAC_node acOp hac, canonACList_eq_map, canonACList_eq_map]
      refine congrArg _ (sortMS_perm_eq ?_)
      simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons]
      -- the flagged inner node canonicalizes to a flagged node; its flatV is its (sorted) args
      have hin : flatV l (canonAC acOp (.sexp l inner)) =
          sortMS ((inner.map (canonAC acOp)).flatMap (flatV l)) := by
        rw [canonAC_node acOp hac, canonACList_eq_map]; simp [flatV]
      rw [hin, ← List.append_assoc]
      exact (List.Perm.append_left _ (sortMS_perm _)).append_right _
  | @appendCong l pre ys ys' h ih =>
      by_cases hac : acOp l
      · rw [canonAC_node acOp hac, canonAC_node acOp hac, canonACList_eq_map, canonACList_eq_map] at *
        refine congrArg _ (sortMS_perm_eq ?_)
        simp only [List.map_append, List.flatMap_append]
        refine List.Perm.append_left _ ?_
        have hp : ((ys.map (canonAC acOp)).flatMap (flatV l)) ~ ((ys'.map (canonAC acOp)).flatMap (flatV l)) :=
          perm_of_sortMS_eq (by injection ih)
        exact hp
      · rw [canonAC_node_neg acOp hac, canonAC_node_neg acOp hac, canonACList_eq_map,
          canonACList_eq_map] at *
        have : ys.map (canonAC acOp) = ys'.map (canonAC acOp) := by injection ih
        simp only [List.map_append, this]
  | @argCong l pre a a' post _ ih =>
      by_cases hac : acOp l
      · rw [canonAC_node acOp hac, canonAC_node acOp hac, canonACList_eq_map, canonACList_eq_map,
          List.map_append, List.map_append, List.map_cons, List.map_cons, ih]
      · rw [canonAC_node_neg acOp hac, canonAC_node_neg acOp hac, canonACList_eq_map,
          canonACList_eq_map, List.map_append, List.map_append, List.map_cons, List.map_cons, ih]
  | @substCongB b b' r v _ ih => rw [canonAC_subst, canonAC_subst, ih]
  | @substCongR b r r' v _ ih => rw [canonAC_subst, canonAC_subst, ih]

/-! ## The decision procedure -/

theorem acEqAC_iff_canonAC {s t : AST} : ACEqAC acOp s t ↔ canonAC acOp s = canonAC acOp t := by
  constructor
  · exact canonAC_complete acOp
  · intro hc
    exact ((hc ▸ (canonAC_sound acOp s).symm).trans (canonAC_sound acOp t))

instance instDecidableACEqAC (s t : AST) : Decidable (ACEqAC acOp s t) :=
  decidable_of_iff _ (acEqAC_iff_canonAC acOp).symm

end MeTTaIL.AC
