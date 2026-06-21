/-
Module: MeTTaILProofs.ACMatch
Layer: Proofs
Purpose: Executable AC-aware matching for the linear collection fragment needed by Cordial Miners. The
  matcher recognizes an AC-headed binary pattern with one fixed subpattern and one rest variable, searches
  the flattened subject collection for a matching leaf, and binds the rest variable to the rebuilt
  remaining collection. Outside that fragment it recurses like the ordinary runtime matcher.
Imports: MeTTaILProofs.ACEngine
Trusted boundary: none
Main exports: matchPatAC, matchPatAC_sound, ACRestFlatSplit, matchPatAC_acRest_witness,
  matchPatAC_acRest_sound, matchPatAC_acRest_complete_of_flat_split,
  matchPatAC_acRest_complete_of_fresh_split, applyBaseRewriteAC, baseReductsAC, oneStepAC',
  oneStepAC'_sound, evalAC', evalAC'_sound
Open obligations: full relation completeness beyond this linear fresh-rest fragment remains open. This
  file proves the soundness bridge and the split-completeness facts used by Cordial Miners.
-/
import MeTTaILProofs.ACEngine
import MeTTaILProofs.DecEq

namespace MeTTaIL.AC

open MeTTaIL

/-- Internal result of AC matching: bindings plus the AC representative matched syntactically. -/
structure ACMatch where
  bnds : List (String × AST)
  witness : AST

/-- Internal list result of AC matching. -/
structure ACMatchList where
  bnds : List (String × AST)
  witnesses : List AST

/-- Pattern for one fixed AC leaf and one rest variable. -/
def acRestPattern (l : Label) (fixed : AST) (restVar : String) : AST :=
  .sexp l [fixed, .var (.base restVar)]

/-- Bind a base variable consistently with the ordinary matcher. -/
def bindBase (v : String) (t : AST) (bnds : List (String × AST)) : Option (List (String × AST)) :=
  match bnds.find? (fun b => b.1 == v) with
  | some (_, t') => if t' == t then some bnds else none
  | none => some ((v, t) :: bnds)

/-- `bindBase` is the ordinary matcher on a base variable. -/
theorem bindBase_eq_matchPat (v : String) (t : AST) (bnds : List (String × AST)) :
    bindBase v t bnds = AST.matchPat (.var (.base v)) t bnds := by
  rfl

/-- Search loop for one AC collection. `preRev` stores leaves already skipped, in reverse order. -/
def matchACRestLoop (l : Label) (fixed : AST) (restVar : String)
    (bnds : List (String × AST)) (preRev : List AST) : List AST → Option ACMatch
  | [] => none
  | leaf :: tail =>
      match AST.matchPat fixed leaf bnds with
      | some bnds' =>
          let rest := rebuild l (preRev.reverse ++ tail)
          match bindBase restVar rest bnds' with
          | some bnds'' => some ⟨bnds'', .sexp l [leaf, rest]⟩
          | none => matchACRestLoop l fixed restVar bnds (leaf :: preRev) tail
      | none => matchACRestLoop l fixed restVar bnds (leaf :: preRev) tail

/-- Search one AC collection for a fixed leaf and bind the rest variable to the rebuilt remainder. -/
def matchACRest (l : Label) (fixed : AST) (restVar : String) (subject : AST)
    (bnds : List (String × AST)) : Option ACMatch :=
  match subject with
  | .sexp m [_, _] => if m == l then matchACRestLoop l fixed restVar bnds [] (flat l subject) else none
  | _ => none

/-- A successful AC-rest search returns a syntactic representative that the ordinary matcher accepts. -/
theorem matchACRestLoop_witness (l : Label) (fixed : AST) (restVar : String)
    (bnds : List (String × AST)) :
    ∀ {preRev leaves : List AST} {r : ACMatch},
      matchACRestLoop l fixed restVar bnds preRev leaves = some r →
      AST.matchPat (acRestPattern l fixed restVar) r.witness bnds = some r.bnds := by
  intro preRev leaves
  induction leaves generalizing preRev with
  | nil =>
      intro r hm
      simp [matchACRestLoop] at hm
  | cons leaf tail ih =>
      intro r hm
      simp only [matchACRestLoop] at hm
      cases hfixed : AST.matchPat fixed leaf bnds with
      | none =>
          simp [hfixed] at hm
          exact ih hm
      | some bnds' =>
          cases hbind : bindBase restVar (rebuild l (preRev.reverse ++ tail)) bnds' with
          | none =>
              simp [hfixed, hbind] at hm
              exact ih hm
          | some bnds'' =>
              simp [hfixed, hbind] at hm
              cases hm
              have hvar :
                  AST.matchPat (.var (.base restVar)) (rebuild l (preRev.reverse ++ tail)) bnds' =
                    some bnds'' := by
                simpa [bindBase_eq_matchPat] using hbind
              simpa [acRestPattern, AST.matchPat, AST.matchPatList, hfixed] using hvar

/-- A successful AC-rest match returns a syntactic representative accepted by the ordinary matcher. -/
theorem matchACRest_witness {l : Label} {fixed : AST} {restVar : String}
    {subject : AST} {bnds : List (String × AST)} {r : ACMatch}
    (hm : matchACRest l fixed restVar subject bnds = some r) :
    AST.matchPat (acRestPattern l fixed restVar) r.witness bnds = some r.bnds := by
  unfold matchACRest at hm
  split at hm
  · next m a b hshape =>
      split at hm
      · exact matchACRestLoop_witness l fixed restVar bnds hm
      · simp at hm
  · simp at hm

/-- If a chosen split of the flattened leaves has a matching fixed leaf and a bindable rebuilt rest, the
    AC-rest search succeeds. This is completeness for the linear search shape, not uniqueness of the
    returned bindings. -/
theorem matchACRestLoop_complete_of_split (l : Label) (fixed : AST) (restVar : String)
    (bnds : List (String × AST)) :
    ∀ {preRev leaves : List AST},
      (∃ pre leaf tail bnds₁ bnds₂,
        leaves = pre ++ leaf :: tail ∧
          AST.matchPat fixed leaf bnds = some bnds₁ ∧
          bindBase restVar (rebuild l (preRev.reverse ++ pre ++ tail)) bnds₁ = some bnds₂) →
      ∃ r, matchACRestLoop l fixed restVar bnds preRev leaves = some r := by
  intro preRev leaves
  induction leaves generalizing preRev with
  | nil =>
      rintro ⟨pre, leaf, tail, bnds₁, bnds₂, hleaves, _, _⟩
      cases pre <;> simp at hleaves
  | cons head rest ih =>
      rintro ⟨pre, leaf, tail, bnds₁, bnds₂, hleaves, hfixed, hbind⟩
      cases pre with
      | nil =>
          simp at hleaves
          rcases hleaves with ⟨rfl, rfl⟩
          have hbind' :
              bindBase restVar (rebuild l (preRev.reverse ++ rest)) bnds₁ = some bnds₂ := by
            simpa using hbind
          refine ⟨⟨bnds₂, .sexp l [head, rebuild l (preRev.reverse ++ rest)]⟩, ?_⟩
          simp [matchACRestLoop, hfixed, hbind']
      | cons skipped pre =>
          simp only [List.cons_append] at hleaves
          injection hleaves with hhead hrest
          subst head
          subst rest
          have hbindTail :
              bindBase restVar (rebuild l ((skipped :: preRev).reverse ++ pre ++ tail))
                bnds₁ = some bnds₂ := by
            simpa [List.reverse_cons, List.append_assoc] using hbind
          have htail :
              ∃ r, matchACRestLoop l fixed restVar bnds (skipped :: preRev)
                (pre ++ leaf :: tail) = some r :=
            ih (preRev := skipped :: preRev)
              ⟨pre, leaf, tail, bnds₁, bnds₂, rfl, hfixed, hbindTail⟩
          simp only [matchACRestLoop]
          cases hhead : AST.matchPat fixed skipped bnds with
          | none =>
              simp
              exact htail
          | some headBnds =>
              cases hheadBind :
                  bindBase restVar (rebuild l (preRev.reverse ++ (pre ++ leaf :: tail))) headBnds with
              | none =>
                  simp [hheadBind]
                  exact htail
              | some headBnds' =>
                  refine ⟨⟨headBnds',
                    .sexp l [skipped, rebuild l (preRev.reverse ++ (pre ++ leaf :: tail))]⟩, ?_⟩
                  simp [hheadBind]

/-- A flattened binary AC subject has a split that the linear AC-rest matcher can use. -/
def ACRestFlatSplit (l : Label) (fixed a b : AST) (restVar : String)
    (bnds : List (String × AST)) : Prop :=
  ∃ pre leaf tail bnds₁ bnds₂,
    flat l (.sexp l [a, b]) = pre ++ leaf :: tail ∧
      AST.matchPat fixed leaf bnds = some bnds₁ ∧
      bindBase restVar (rebuild l (pre ++ tail)) bnds₁ = some bnds₂

/-- Completeness for one binary AC subject, stated over a split of its flattened leaves. -/
theorem matchACRest_complete_of_flat_split {l : Label} {fixed a b : AST} {restVar : String}
    {bnds : List (String × AST)} (h : ACRestFlatSplit l fixed a b restVar bnds) :
    ∃ r, matchACRest l fixed restVar (.sexp l [a, b]) bnds = some r := by
  unfold matchACRest
  simp
  exact matchACRestLoop_complete_of_split l fixed restVar bnds h

/-- Moving the selected AC leaf to the head preserves the rebuilt collection modulo AC. -/
theorem rebuild_middle_ac (acOp : Label → Bool) {l : Label} (hac : acOp l = true)
    (leaf : AST) (pre tail : List AST) (hrest : pre ++ tail ≠ []) :
    ACEq acOp (rebuild l (pre ++ leaf :: tail)) (.sexp l [leaf, rebuild l (pre ++ tail)]) := by
  have hperm : ACEq acOp (rebuild l (pre ++ leaf :: tail))
      (rebuild l (leaf :: (pre ++ tail))) :=
    rebuild_perm acOp hac (List.perm_middle (a := leaf) (l₁ := pre) (l₂ := tail))
  have hhead : rebuild l (leaf :: (pre ++ tail)) = .sexp l [leaf, rebuild l (pre ++ tail)] := by
    rw [rebuild_cons hrest]
  simpa [hhead] using hperm

/-- The AC-rest search witness is AC-equivalent to the rebuilt leaves being searched, provided the
    collection still has at least two leaves. That invariant is true for binary AC subjects. -/
theorem matchACRestLoop_acEq (acOp : Label → Bool) {l : Label} (hac : acOp l = true)
    (fixed : AST) (restVar : String) (bnds : List (String × AST)) :
    ∀ {preRev leaves : List AST} {r : ACMatch},
      2 ≤ (preRev.reverse ++ leaves).length →
      matchACRestLoop l fixed restVar bnds preRev leaves = some r →
      ACEq acOp (rebuild l (preRev.reverse ++ leaves)) r.witness := by
  intro preRev leaves
  induction leaves generalizing preRev with
  | nil =>
      intro r _ hm
      simp [matchACRestLoop] at hm
  | cons leaf tail ih =>
      intro r hlen hm
      have hlenTail : 2 ≤ ((leaf :: preRev).reverse ++ tail).length := by
        simpa [List.reverse_cons, List.append_assoc] using hlen
      simp only [matchACRestLoop] at hm
      cases hfixed : AST.matchPat fixed leaf bnds with
      | none =>
          simp [hfixed] at hm
          simpa [List.reverse_cons, List.append_assoc] using ih hlenTail hm
      | some bnds' =>
          cases hbind : bindBase restVar (rebuild l (preRev.reverse ++ tail)) bnds' with
          | none =>
              simp [hfixed, hbind] at hm
              simpa [List.reverse_cons, List.append_assoc] using ih hlenTail hm
          | some _ =>
              simp [hfixed, hbind] at hm
              cases hm
              have hrest : preRev.reverse ++ tail ≠ [] := by
                intro hnil
                have hlenOne : (preRev.reverse ++ leaf :: tail).length = 1 := by
                  have hlenRest : (preRev.reverse ++ tail).length = 0 := by
                    rw [hnil]
                    rfl
                  have hlenAll : (preRev.reverse ++ leaf :: tail).length =
                      (preRev.reverse ++ tail).length + 1 := by
                    simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  rw [hlenAll, hlenRest]
                have hnot : ¬ 2 ≤ (preRev.reverse ++ leaf :: tail).length := by
                  rw [hlenOne]
                  decide
                exact hnot hlen
              simpa using rebuild_middle_ac acOp hac leaf preRev.reverse tail hrest

/-- A binary AC subject has at least two flattened leaves. -/
theorem flat_binary_length_two (l : Label) (a b : AST) :
    2 ≤ (flat l (.sexp l [a, b])).length := by
  rw [flat_node]
  have ha : flat l a ≠ [] := flat_ne_nil l a
  have hb : flat l b ≠ [] := flat_ne_nil l b
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil ha
  obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hb
  rw [hx, hy]
  simp
  omega

/-- A successful AC-rest match returns a representative AC-equivalent to the subject. -/
theorem matchACRest_acEq {acOp : Label → Bool} {l : Label} (hac : acOp l = true)
    {fixed : AST} {restVar : String} {subject : AST} {bnds : List (String × AST)} {r : ACMatch}
    (hm : matchACRest l fixed restVar subject bnds = some r) :
    ACEq acOp subject r.witness := by
  cases subject with
  | var p => simp [matchACRest] at hm
  | subst body repl v => simp [matchACRest] at hm
  | sexp m args =>
      cases args with
      | nil => simp [matchACRest] at hm
      | cons a rest =>
          cases rest with
          | nil => simp [matchACRest] at hm
          | cons b restTail =>
              cases restTail with
              | nil =>
                  cases hml : (m == l)
                  · simp [matchACRest, hml] at hm
                  · have hmeq : m = l := LawfulBEq.eq_of_beq hml
                    subst m
                    simp [matchACRest] at hm
                    have hloop :
                        ACEq acOp (rebuild l (flat l (.sexp l [a, b]))) r.witness :=
                      matchACRestLoop_acEq acOp hac fixed restVar bnds
                        (flat_binary_length_two l a b) hm
                    exact (rebuild_flat acOp hac (.sexp l [a, b])).symm.trans hloop
              | cons c more => simp [matchACRest] at hm

mutual
  /-- AC-aware first-order matching. The AC-specific case is linear: one fixed subpattern and one rest
      variable under an AC binary collection. -/
  def matchPatACRaw (acOp : Label → Bool) : AST → AST → List (String × AST) → Option ACMatch
    | .var (.base v), t, bnds => (bindBase v t bnds).map (fun bnds' => ⟨bnds', t⟩)
    | .sexp l [fixed, .var (.base restVar)], t, bnds =>
        if acOp l then
          matchACRest l fixed restVar t bnds
        else
          match t with
          | .sexp m ts =>
              if l == m then
                (matchPatACRawList acOp [fixed, .var (.base restVar)] ts bnds).map
                  (fun r => ⟨r.bnds, .sexp m r.witnesses⟩)
              else none
          | _ => none
    | .sexp l ps, .sexp m ts, bnds =>
        if l == m then
          (matchPatACRawList acOp ps ts bnds).map (fun r => ⟨r.bnds, .sexp m r.witnesses⟩)
        else none
    | .subst pb pr pv, .subst tb tr tv, bnds =>
        if pv == tv then
          (matchPatACRaw acOp pb tb bnds).bind fun rb =>
            (matchPatACRaw acOp pr tr rb.bnds).map fun rr =>
              ⟨rr.bnds, .subst rb.witness rr.witness tv⟩
        else none
    | p, t, bnds => if p == t then some ⟨bnds, t⟩ else none
  /-- Pointwise AC-aware matching for argument lists. -/
  def matchPatACRawList (acOp : Label → Bool) :
      List AST → List AST → List (String × AST) → Option ACMatchList
    | [], [], bnds => some ⟨bnds, []⟩
    | p :: ps, t :: ts, bnds =>
        (matchPatACRaw acOp p t bnds).bind fun rp =>
          (matchPatACRawList acOp ps ts rp.bnds).map fun rs =>
            ⟨rs.bnds, rp.witness :: rs.witnesses⟩
    | _, _, _ => none
end

/-- Public AC-aware matcher. -/
def matchPatAC (acOp : Label → Bool) (pat t : AST) (bnds : List (String × AST)) :
    Option (List (String × AST)) :=
  (matchPatACRaw acOp pat t bnds).map (fun r => r.bnds)

/-- A successful linear AC-rest match has an AC-equivalent syntactic representative accepted by the
    ordinary matcher. -/
theorem matchPatACRaw_acRest_sound {acOp : Label → Bool} {l : Label} {fixed subject : AST}
    {restVar : String} {bnds : List (String × AST)} {r : ACMatch} (hac : acOp l = true)
    (hm : matchPatACRaw acOp (acRestPattern l fixed restVar) subject bnds = some r) :
    ACEq acOp subject r.witness ∧
      AST.matchPat (acRestPattern l fixed restVar) r.witness bnds = some r.bnds := by
  have hrest : matchACRest l fixed restVar subject bnds = some r := by
    simpa [acRestPattern, matchPatACRaw, hac] using hm
  exact ⟨matchACRest_acEq hac hrest, matchACRest_witness hrest⟩

/-- A successful linear AC-rest match has a syntactic representative accepted by the ordinary matcher. -/
theorem matchPatACRaw_acRest_witness {acOp : Label → Bool} {l : Label} {fixed subject : AST}
    {restVar : String} {bnds : List (String × AST)} {r : ACMatch} (hac : acOp l = true)
    (hm : matchPatACRaw acOp (acRestPattern l fixed restVar) subject bnds = some r) :
    AST.matchPat (acRestPattern l fixed restVar) r.witness bnds = some r.bnds := by
  exact (matchPatACRaw_acRest_sound hac hm).2

/-- Lift a public AC-rest match back to the raw matcher result it erased. -/
theorem matchPatAC_acRest_raw {acOp : Label → Bool} {l : Label} {fixed subject : AST}
    {restVar : String} {bnds bnds' : List (String × AST)}
    (hm : matchPatAC acOp (acRestPattern l fixed restVar) subject bnds = some bnds') :
    ∃ r, matchPatACRaw acOp (acRestPattern l fixed restVar) subject bnds = some r ∧
      r.bnds = bnds' := by
  unfold matchPatAC at hm
  cases hraw : matchPatACRaw acOp (acRestPattern l fixed restVar) subject bnds with
  | none => simp [hraw] at hm
  | some r =>
      simp [hraw] at hm
      exact ⟨r, rfl, hm⟩

/-- Public soundness bridge for the linear AC-rest fragment used by Cordial Miners. -/
theorem matchPatAC_acRest_sound {acOp : Label → Bool} {l : Label} {fixed subject : AST}
    {restVar : String} {bnds bnds' : List (String × AST)} (hac : acOp l = true)
    (hm : matchPatAC acOp (acRestPattern l fixed restVar) subject bnds = some bnds') :
    ∃ witness,
      ACEq acOp subject witness ∧
      AST.matchPat (acRestPattern l fixed restVar) witness bnds = some bnds' := by
  obtain ⟨r, hraw, hr⟩ := matchPatAC_acRest_raw hm
  subst bnds'
  have hs := matchPatACRaw_acRest_sound hac hraw
  exact ⟨r.witness, hs.1, hs.2⟩

/-- Public witness theorem for the linear AC-rest fragment used by Cordial Miners. -/
theorem matchPatAC_acRest_witness {acOp : Label → Bool} {l : Label} {fixed subject : AST}
    {restVar : String} {bnds bnds' : List (String × AST)} (hac : acOp l = true)
    (hm : matchPatAC acOp (acRestPattern l fixed restVar) subject bnds = some bnds') :
    ∃ witness, AST.matchPat (acRestPattern l fixed restVar) witness bnds = some bnds' := by
  obtain ⟨witness, _, hmatch⟩ := matchPatAC_acRest_sound hac hm
  exact ⟨witness, hmatch⟩

/-- Public completeness theorem for the linear AC-rest fragment. If the flattened binary AC subject has
    a split whose selected leaf matches the fixed subpattern and whose remaining leaves bind to the rest
    variable, the AC-aware matcher returns some bindings. -/
theorem matchPatAC_acRest_complete_of_flat_split {acOp : Label → Bool} {l : Label}
    {fixed a b : AST} {restVar : String} {bnds : List (String × AST)} (hac : acOp l = true)
    (h : ACRestFlatSplit l fixed a b restVar bnds) :
    ∃ bnds', matchPatAC acOp (acRestPattern l fixed restVar) (.sexp l [a, b]) bnds = some bnds' := by
  obtain ⟨r, hr⟩ := matchACRest_complete_of_flat_split h
  exact ⟨r.bnds, by simp [matchPatAC, acRestPattern, matchPatACRaw, hac, hr]⟩

/-- A fresh rest variable can always bind to the rebuilt complement of a selected AC leaf. -/
private theorem bindBase_fresh {v : String} {t : AST} {bnds : List (String × AST)}
    (hfresh : bnds.find? (fun b => b.1 == v) = none) :
    bindBase v t bnds = some ((v, t) :: bnds) := by
  simp [bindBase, hfresh]

/-- Public completeness theorem for the common linear AC-rest case. If a selected flattened leaf matches
    the fixed subpattern and the rest variable is fresh after that match, the AC-aware matcher succeeds.
    This is the Cordial Miners rule shape: one observed fact or event, and one variable for the rest of
    the collection. -/
theorem matchPatAC_acRest_complete_of_fresh_split {acOp : Label → Bool} {l : Label}
    {fixed a b : AST} {restVar : String} {bnds : List (String × AST)}
    {pre tail : List AST} {leaf : AST} {bnds₁ : List (String × AST)}
    (hac : acOp l = true)
    (hflat : flat l (.sexp l [a, b]) = pre ++ leaf :: tail)
    (hfixed : AST.matchPat fixed leaf bnds = some bnds₁)
    (hfresh : bnds₁.find? (fun b => b.1 == restVar) = none) :
    ∃ bnds', matchPatAC acOp (acRestPattern l fixed restVar) (.sexp l [a, b]) bnds = some bnds' := by
  have hbind :
      bindBase restVar (rebuild l (pre ++ tail)) bnds₁ =
        some ((restVar, rebuild l (pre ++ tail)) :: bnds₁) :=
    bindBase_fresh hfresh
  exact matchPatAC_acRest_complete_of_flat_split hac
    ⟨pre, leaf, tail, bnds₁, (restVar, rebuild l (pre ++ tail)) :: bnds₁,
      hflat, hfixed, hbind⟩

/-- Lift a successful argument-list match into the enclosing `sexp` matcher case. -/
private theorem matchPatACRaw_sound_sexp {acOp : Label → Bool}
    {l m : Label} {ps ts : List AST} {bnds : List (String × AST)} {rs : ACMatchList}
    (hlabel : (l == m) = true)
    (hs : List.Forall₂ (ACEq acOp) ts rs.witnesses ∧
      AST.matchPatList ps rs.witnesses bnds = some rs.bnds) :
    ACEq acOp (.sexp m ts) (.sexp m rs.witnesses) ∧
      AST.matchPat (.sexp l ps) (.sexp m rs.witnesses) bnds = some rs.bnds := by
  have hlabelEq : l = m := LawfulBEq.eq_of_beq hlabel
  subst m
  exact ⟨ACEq.sexpCongr acOp hs.1, by simpa [AST.matchPat] using hs.2⟩

/-- Raw AC-aware matcher soundness. A successful match returns an AC-equivalent witness accepted by
    the ordinary matcher. -/
theorem matchPatACRaw_sound (acOp : Label → Bool) :
    ∀ (pat t : AST) (bnds : List (String × AST)) (r : ACMatch),
      matchPatACRaw acOp pat t bnds = some r →
      ACEq acOp t r.witness ∧ AST.matchPat pat r.witness bnds = some r.bnds := by
  exact matchPatACRaw.induct acOp
    (fun pat t bnds =>
      ∀ r, matchPatACRaw acOp pat t bnds = some r →
        ACEq acOp t r.witness ∧ AST.matchPat pat r.witness bnds = some r.bnds)
    (fun ps ts bnds =>
      ∀ r, matchPatACRawList acOp ps ts bnds = some r →
        List.Forall₂ (ACEq acOp) ts r.witnesses ∧
          AST.matchPatList ps r.witnesses bnds = some r.bnds)
    (by
      intro v t bnds r hm
      simp only [matchPatACRaw] at hm
      cases hbind : bindBase v t bnds with
      | none =>
          simp [hbind] at hm
      | some bnds' =>
          simp [hbind] at hm
          cases hm
          exact ⟨ACEq.refl t, by simpa [bindBase_eq_matchPat] using hbind⟩)
    (by
      intro l fixed restVar t bnds hac r hm
      exact matchPatACRaw_acRest_sound hac hm)
    (by
      intro l fixed restVar bnds hno m ts hlabel ih r hm
      simp [matchPatACRaw, hno, hlabel] at hm
      cases hlist :
          matchPatACRawList acOp [fixed, AST.var (DottedPath.base restVar)] ts bnds with
      | none =>
          simp [hlist] at hm
      | some rs =>
          simp [hlist] at hm
          cases hm
          exact matchPatACRaw_sound_sexp hlabel (ih rs hlist))
    (by
      intro l fixed restVar bnds hno m ts hlabel r hm
      simp [matchPatACRaw, hno, hlabel] at hm)
    (by
      intro l fixed restVar t bnds hno hnot r hm
      simp [matchPatACRaw, hno] at hm)
    (by
      intro l ps m ts bnds hnot hlabel ih r hm
      simp [matchPatACRaw, hlabel] at hm
      cases hlist : matchPatACRawList acOp ps ts bnds with
      | none =>
          simp [hlist] at hm
      | some rs =>
          simp [hlist] at hm
          cases hm
          exact matchPatACRaw_sound_sexp hlabel (ih rs hlist))
    (by
      intro l ps m ts bnds hnot hlabel r hm
      simp [matchPatACRaw, hlabel] at hm)
    (by
      intro pb pr pv tb tr tv bnds hlabel ihb ihr r hm
      simp [matchPatACRaw, hlabel] at hm
      cases hb : matchPatACRaw acOp pb tb bnds with
      | none =>
          simp [hb] at hm
      | some rb =>
          cases hr : matchPatACRaw acOp pr tr rb.bnds with
          | none =>
              simp [hb, hr] at hm
          | some rr =>
              simp [hb, hr] at hm
              cases hm
              have hpv : pv = tv := LawfulBEq.eq_of_beq hlabel
              subst tv
              obtain ⟨hbAc, hbMatch⟩ := ihb rb hb
              obtain ⟨hrAc, hrMatch⟩ := ihr rb rr hr
              exact ⟨(ACEq.substCongB hbAc).trans (ACEq.substCongR hrAc),
                by simpa [AST.matchPat, hlabel, hbMatch] using hrMatch⟩)
    (by
      intro pb pr pv tb tr tv bnds hlabel r hm
      simp [matchPatACRaw, hlabel] at hm)
    (by
      intro p t bnds hvar hac hsexp hsubst heq r hm
      simp [matchPatACRaw, heq] at hm
      cases hm
      exact ⟨ACEq.refl t, by simp [AST.matchPat, heq]⟩)
    (by
      intro p t bnds hvar hac hsexp hsubst heq r hm
      simp [matchPatACRaw, heq] at hm)
    (by
      intro bnds r hm
      simp [matchPatACRawList] at hm
      cases hm
      exact ⟨List.Forall₂.nil, rfl⟩)
    (by
      intro p ps t ts bnds ihp ihps r hm
      simp [matchPatACRawList] at hm
      cases hp : matchPatACRaw acOp p t bnds with
      | none =>
          simp [hp] at hm
      | some rp =>
          cases hs : matchPatACRawList acOp ps ts rp.bnds with
          | none =>
              simp [hp, hs] at hm
          | some rs =>
              simp [hp, hs] at hm
              cases hm
              obtain ⟨hpAc, hpMatch⟩ := ihp rp hp
              obtain ⟨hsAc, hsMatch⟩ := ihps rp rs hs
              exact ⟨List.Forall₂.cons hpAc hsAc, by simpa [AST.matchPatList, hpMatch] using hsMatch⟩)
    (by
      intro ps ts bnds hnil hcons r hm
      simp [matchPatACRawList] at hm)

/-- Public AC-aware matcher soundness. -/
theorem matchPatAC_sound {acOp : Label → Bool} {pat subject : AST}
    {bnds bnds' : List (String × AST)}
    (hm : matchPatAC acOp pat subject bnds = some bnds') :
    ∃ witness, ACEq acOp subject witness ∧ AST.matchPat pat witness bnds = some bnds' := by
  unfold matchPatAC at hm
  cases hraw : matchPatACRaw acOp pat subject bnds with
  | none =>
      simp [hraw] at hm
  | some r =>
      simp [hraw] at hm
      subst bnds'
      exact ⟨r.witness, matchPatACRaw_sound acOp pat subject bnds r hraw⟩

/-- Apply one premise-free rewrite using AC-aware matching. -/
def applyBaseRewriteAC (acOp : Label → Bool) (rd : RewriteDecl) (t : AST) : Option AST :=
  match rd.rw with
  | .base lhs rhs => (matchPatAC acOp lhs t []).map (fun bnds => AST.inst bnds rhs)
  | .ctx _ _ => none

/-- Every top-level AC-aware base reduct of a term. -/
def baseReductsAC (acOp : Label → Bool) (p : Presentation) (t : AST) : List AST :=
  p.rewrites.filterMap (fun rd => applyBaseRewriteAC acOp rd t)

/-- Every AC-aware base rewrite has an AC-equivalent ordinary-rewrite witness. -/
theorem reduces_of_applyBaseRewriteAC {acOp : Label → Bool} {p : Presentation}
    {rd : RewriteDecl} {t t' : AST}
    (hmem : rd ∈ p.rewrites) (h : applyBaseRewriteAC acOp rd t = some t') :
    ∃ witness, ACEq acOp t witness ∧ Reduces p witness t' := by
  cases hrw : rd.rw with
  | base lhs rhs =>
      simp [applyBaseRewriteAC, hrw] at h
      obtain ⟨bnds, hmatchAC, heq⟩ := h
      obtain ⟨witness, hac, hmatch⟩ := matchPatAC_sound hmatchAC
      exact ⟨witness, hac, heq ▸ reduces_base p rd lhs rhs witness bnds hmem hrw hmatch⟩
  | ctx hyp r =>
      simp [applyBaseRewriteAC, hrw] at h

/-- Every member of `baseReductsAC` has an AC-equivalent ordinary-rewrite witness. -/
theorem reduces_of_mem_baseReductsAC {acOp : Label → Bool} {p : Presentation} {t t' : AST}
    (h : t' ∈ baseReductsAC acOp p t) :
    ∃ witness, ACEq acOp t witness ∧ Reduces p witness t' := by
  simp only [baseReductsAC, List.mem_filterMap] at h
  obtain ⟨rd, hmem, happly⟩ := h
  exact reduces_of_applyBaseRewriteAC hmem happly

/-- A top-level executable AC-aware reduct is a genuine rewrite modulo AC. -/
theorem rewStepModAC_of_mem_baseReductsAC {acOp : Label → Bool} {p : Presentation} {t t' : AST}
    (h : t' ∈ baseReductsAC acOp p t) :
    RewStepModAC acOp p t t' := by
  obtain ⟨witness, hac, hred⟩ := reduces_of_mem_baseReductsAC h
  exact ⟨witness, t', hac, RewStep.top hred, ACEq.refl t'⟩

/-- Lift a rewrite modulo AC through one `sexp` argument context. -/
theorem rewStepModAC_arg {acOp : Label → Bool} {p : Presentation} {l : Label}
    {pre post : List AST} {a a' : AST} (h : RewStepModAC acOp p a a') :
    RewStepModAC acOp p (.sexp l (pre ++ a :: post)) (.sexp l (pre ++ a' :: post)) := by
  obtain ⟨u, u', hac, hstep, hac'⟩ := h
  exact ⟨.sexp l (pre ++ u :: post), .sexp l (pre ++ u' :: post),
    ACEq.argCong pre post hac, RewStep.arg hstep, ACEq.argCong pre post hac'⟩

/-- Lift a rewrite modulo AC through the body of a `subst` node. -/
theorem rewStepModAC_substB {acOp : Label → Bool} {p : Presentation}
    {b b' r : AST} {v : DottedPath} (h : RewStepModAC acOp p b b') :
    RewStepModAC acOp p (.subst b r v) (.subst b' r v) := by
  obtain ⟨u, u', hac, hstep, hac'⟩ := h
  exact ⟨.subst u r v, .subst u' r v,
    ACEq.substCongB hac, RewStep.substB hstep, ACEq.substCongB hac'⟩

/-- Lift a rewrite modulo AC through the replacement of a `subst` node. -/
theorem rewStepModAC_substR {acOp : Label → Bool} {p : Presentation}
    {b r r' : AST} {v : DottedPath} (h : RewStepModAC acOp p r r') :
    RewStepModAC acOp p (.subst b r v) (.subst b r' v) := by
  obtain ⟨u, u', hac, hstep, hac'⟩ := h
  exact ⟨.subst b u v, .subst b u' v,
    ACEq.substCongR hac, RewStep.substR hstep, ACEq.substCongR hac'⟩

mutual
  /-- One leftmost-outermost step using AC-aware matching at every visited node. -/
  def oneStepAC' (acOp : Label → Bool) (p : Presentation) : AST → Option AST
    | .var x =>
        match baseReductsAC acOp p (.var x) with
        | r :: _ => some r
        | [] => none
    | .sexp l args =>
        match baseReductsAC acOp p (.sexp l args) with
        | r :: _ => some r
        | [] => (oneStepACList' acOp p args).map (fun args' => .sexp l args')
    | .subst b r v =>
        match baseReductsAC acOp p (.subst b r v) with
        | s :: _ => some s
        | [] =>
            match oneStepAC' acOp p b with
            | some b' => some (.subst b' r v)
            | none => (oneStepAC' acOp p r).map (fun r' => .subst b r' v)
  /-- One AC-aware step inside the first reducible list element. -/
  def oneStepACList' (acOp : Label → Bool) (p : Presentation) : List AST → Option (List AST)
    | [] => none
    | a :: as =>
        match oneStepAC' acOp p a with
        | some a' => some (a' :: as)
        | none => (oneStepACList' acOp p as).map (fun as' => a :: as')
end

/-- Fuel-bounded evaluation using the AC-aware stepper. -/
def evalAC' (acOp : Label → Bool) (p : Presentation) : Nat → AST → AST
  | 0, t => t
  | n + 1, t =>
      match oneStepAC' acOp p t with
      | some t' => evalAC' acOp p n t'
      | none => t

mutual
  /-- Soundness: every executable AC-aware one-step reduct is a genuine rewrite modulo AC. -/
  theorem oneStepAC'_sound (acOp : Label → Bool) (p : Presentation) :
      ∀ (t : AST) {t' : AST}, oneStepAC' acOp p t = some t' → RewStepModAC acOp p t t'
    | .var x, t', h => by
        simp only [oneStepAC'] at h
        split at h
        · rename_i r rs heq
          cases h
          exact rewStepModAC_of_mem_baseReductsAC (by rw [heq]; exact List.mem_cons_self ..)
        · exact absurd h (by simp)
    | .sexp l args, t', h => by
        simp only [oneStepAC'] at h
        split at h
        · rename_i r rs heq
          cases h
          exact rewStepModAC_of_mem_baseReductsAC (by rw [heq]; exact List.mem_cons_self ..)
        · rcases hopt : oneStepACList' acOp p args with _ | args'
          · rw [hopt] at h; simp at h
          · rw [hopt] at h; simp only [Option.map_some] at h
            cases h
            obtain ⟨pre, a, a', post, hargs, hargs', hstep⟩ :=
              oneStepACList'_sound acOp p args hopt
            subst hargs; subst hargs'
            exact rewStepModAC_arg hstep
    | .subst b r v, t', h => by
        simp only [oneStepAC'] at h
        split at h
        · rename_i s ss heq
          cases h
          exact rewStepModAC_of_mem_baseReductsAC (by rw [heq]; exact List.mem_cons_self ..)
        · split at h
          · rename_i b' hb
            cases h
            exact rewStepModAC_substB (oneStepAC'_sound acOp p b hb)
          · rename_i hb
            rcases hopt : oneStepAC' acOp p r with _ | r'
            · rw [hopt] at h; simp at h
            · rw [hopt] at h; simp only [Option.map_some] at h
              cases h
              exact rewStepModAC_substR (oneStepAC'_sound acOp p r hopt)
  /-- Soundness for the AC-aware list stepper. -/
  theorem oneStepACList'_sound (acOp : Label → Bool) (p : Presentation) :
      ∀ (args : List AST) {args' : List AST}, oneStepACList' acOp p args = some args' →
        ∃ (pre : List AST) (a a' : AST) (post : List AST),
          args = pre ++ a :: post ∧ args' = pre ++ a' :: post ∧ RewStepModAC acOp p a a'
    | [], args', h => by simp [oneStepACList'] at h
    | a :: as, args', h => by
        simp only [oneStepACList'] at h
        split at h
        · rename_i a' ha
          cases h
          exact ⟨[], a, a', as, rfl, rfl, oneStepAC'_sound acOp p a ha⟩
        · rename_i ha
          rcases hopt : oneStepACList' acOp p as with _ | as'
          · rw [hopt] at h; simp at h
          · rw [hopt] at h; simp only [Option.map_some] at h
            cases h
            obtain ⟨pre, b, b', post, hpre, hpost, hstep⟩ :=
              oneStepACList'_sound acOp p as hopt
            subst hpre; subst hpost
            exact ⟨a :: pre, b, b', post, rfl, rfl, hstep⟩
end

/-- Soundness of fuel-bounded AC-aware evaluation. -/
theorem evalAC'_sound (acOp : Label → Bool) (p : Presentation) (fuel : Nat) (t : AST) :
    Relation.ReflTransGen (RewStepModAC acOp p) t (evalAC' acOp p fuel t) := by
  induction fuel generalizing t with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      cases hs : oneStepAC' acOp p t with
      | none =>
          rw [show evalAC' acOp p (n + 1) t = t from by simp [evalAC', hs]]
      | some t' =>
          rw [show evalAC' acOp p (n + 1) t = evalAC' acOp p n t' from by simp [evalAC', hs]]
          exact (Relation.ReflTransGen.single (oneStepAC'_sound acOp p t hs)).trans (ih t')

end MeTTaIL.AC
