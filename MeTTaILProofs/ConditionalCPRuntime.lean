/-
Module: MeTTaILProofs.ConditionalCPRuntime
Layer: Proofs
Purpose: Connect the premised (conditional/congruence) rewrite fragment to the ACTUAL runtime relation, the
  conditional analog of `CPRuntime` (which bridges the unconditional first-order critical-pair theory to the
  runtime `RewStep`). The runtime's premised rewrites are the congruence/context rules: a premise
  `let src ~> tgt in C[src] ~> C[tgt]` fires by reducing the subterm bound to `src` and rebuilding the
  context. The key fact this module proves is that runtime congruence schemas, including `sexp` arguments
  and the two `Subst` components, are reproducible as base context steps of the runtime's own `RewStep`
  closure. Hence adding the premised `sexp` congruence rules used by presentations does not enlarge the
  reachability of `RewStep` on the embedded fragment, so the unconditional confluence transported by
  `CPRuntime.RewStep_confluent_on_emb` already certifies the runtime relation with that congruence extension.

  Why this route, not a direct `CRstep` bisimulation. The runtime's `PremisesHold` uses a ONE-step premise
  (`Reduces`, forced by strict positivity of the inductive: `ReflTransGen (Reduces)` in a premise is not
  strictly positive), whereas the abstract conditional rewriting of `ConditionalCP` uses level-stratified
  MANY-step conditions. These are genuinely different conditional-rewriting models. For the congruence rules
  the runtime actually uses, the premise is exactly "the subterm reduces", which is the runtime's own context
  closure, so the faithful and complete connection is to the unconditional positional rewriting that
  `CPRuntime` already bridges. `Confluent` depends only on a relation's reflexive-transitive closure, so the
  transport is a closure-squeeze: a relation squeezed between `r1` and `ReflTransGen r1` has `r1`'s closure,
  hence `r1`'s confluence.
Imports: MeTTaILProofs.CPRuntime (the unconditional bridge: emb, embPres, RewStep_confluent_on_emb), the
  runtime relation `RewStep`/`Reduces`/`PremisesHold`.
Trusted boundary: none (fully proved)
Main exports: reflTransGen_eq_of_squeeze, confluent_of_reflTransGen_eq, confluent_squeeze
Open obligations: none for the runtime congruence fragment proved here; genuine NON-congruence
  multi-step side conditions exceed the runtime's one-step-premise encoding and are covered abstractly by
  `ConditionalCP` over the first-order model instead.
-/
import MeTTaILProofs.CPRuntime
import MeTTaILProofs.CPDemo

namespace MeTTaIL.CP

open Relation

variable (ν : Nat → String)

/-! ### Closure-squeeze: confluence depends only on the reflexive-transitive closure

`Confluent r` is stated entirely through `ReflTransGen r` (a divergence of closures is joined by closures),
so two relations with the same reflexive-transitive closure are confluent together. The useful way to get
that equality is a squeeze: if `r1 ⊆ r2 ⊆ ReflTransGen r1`, then `ReflTransGen r1 = ReflTransGen r2`. -/

variable {α : Type*}

/-- A relation squeezed between `r1` and its reflexive-transitive closure has the same closure as `r1`. -/
theorem reflTransGen_eq_of_squeeze {r1 r2 : α → α → Prop}
    (h12 : ∀ a b, r1 a b → r2 a b) (h21 : ∀ a b, r2 a b → ReflTransGen r1 a b) :
    ∀ {a b : α}, ReflTransGen r2 a b ↔ ReflTransGen r1 a b := by
  intro a b
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.trans (h21 _ _ hstep)
  · intro h
    exact h.mono (fun _ _ hab => h12 _ _ hab)

/-- Joinability transfers across relations with equal reflexive-transitive closures. -/
theorem joinable_of_reflTransGen_eq {r1 r2 : α → α → Prop}
    (heq : ∀ {a b : α}, ReflTransGen r2 a b ↔ ReflTransGen r1 a b) {a b : α}
    (h : Joinable r1 a b) : Joinable r2 a b := by
  obtain ⟨c, hac, hbc⟩ := h
  exact ⟨c, heq.mpr hac, heq.mpr hbc⟩

/-- Confluence transfers across relations with equal reflexive-transitive closures. -/
theorem confluent_of_reflTransGen_eq {r1 r2 : α → α → Prop}
    (heq : ∀ {a b : α}, ReflTransGen r2 a b ↔ ReflTransGen r1 a b) (h : Confluent r1) :
    Confluent r2 := by
  intro a b c hab hac
  exact joinable_of_reflTransGen_eq heq (h a b c (heq.mp hab) (heq.mp hac))

/-- Confluence transfers under a squeeze `r1 ⊆ r2 ⊆ ReflTransGen r1`: if `r1` is confluent so is `r2`. The
    bigger relation `r2` adds only steps that `r1` could already reach, so it has the same normal-form
    structure. This is how a presentation's premised congruence rules inherit confluence from the base
    rules: each premised-congruence step is a base context step, so the base relation `r1` and the extended
    relation `r2` are squeezed together. -/
theorem confluent_squeeze {r1 r2 : α → α → Prop}
    (h12 : ∀ a b, r1 a b → r2 a b) (h21 : ∀ a b, r2 a b → ReflTransGen r1 a b)
    (h : Confluent r1) : Confluent r2 :=
  confluent_of_reflTransGen_eq (reflTransGen_eq_of_squeeze h12 h21) h

/-! ### Lifting a runtime reduction sequence under a context

`RewStep` is closed under the `sexp`-argument and `Subst` contexts (its `arg`/`substB`/`substR`
constructors). These lemmas lift a WHOLE reduction sequence under each context, the multi-step form needed
to show a congruence step (which reduces a subterm and rebuilds the context) is a base context reduction. -/

/-- A reduction sequence lifts under an `sexp`-argument context. -/
theorem rewStepMany_arg (p : Presentation) {l : Label} {pre post : List AST} {a a' : AST}
    (h : ReflTransGen (RewStep p) a a') :
    ReflTransGen (RewStep p) (.sexp l (pre ++ a :: post)) (.sexp l (pre ++ a' :: post)) :=
  ReflTransGen.lift (fun x => AST.sexp l (pre ++ x :: post)) (fun _ _ hst => RewStep.arg hst) h

/-- A reduction sequence lifts under the body of a `Subst` context. -/
theorem rewStepMany_substB (p : Presentation) {r : AST} {v : DottedPath} {b b' : AST}
    (h : ReflTransGen (RewStep p) b b') :
    ReflTransGen (RewStep p) (.subst b r v) (.subst b' r v) :=
  ReflTransGen.lift (fun x => AST.subst x r v) (fun _ _ hst => RewStep.substB hst) h

/-- A reduction sequence lifts under the replacement of a `Subst` context. -/
theorem rewStepMany_substR (p : Presentation) {b : AST} {v : DottedPath} {r r' : AST}
    (h : ReflTransGen (RewStep p) r r') :
    ReflTransGen (RewStep p) (.subst b r v) (.subst b r' v) :=
  ReflTransGen.lift (fun x => AST.subst b x v) (fun _ _ hst => RewStep.substR hst) h

/-- A semantic congruence premise lifts to the matching `sexp` argument context. -/
theorem sexpArgCong_squeeze_of_inner {base : Presentation} {lab : Label}
    {pre post : List AST} {a B : AST} (hinner : ReflTransGen (RewStep base) a B) :
    ReflTransGen (RewStep base)
      (.sexp lab (pre ++ a :: post)) (.sexp lab (pre ++ B :: post)) :=
  rewStepMany_arg base hinner

/-! ### Runtime congruence schemas

These are the context shapes the runtime relation actually has. Presentation-level premised rules use the
`sexp` argument shape. `Subst` body and replacement contexts live directly in `RewStep`, because
instantiating a top-level `Subst` right-hand side resolves the substitution rather than rebuilding the node. -/

/-- An already-instantiated runtime congruence step, covering `sexp` arguments and both `Subst`
    components. The inner relation is a base runtime reduction sequence. -/
inductive RuntimeCongruenceStep (base : Presentation) : AST → AST → Prop where
  | sexpArg {l : Label} {pre post : List AST} {a a' : AST} :
      ReflTransGen (RewStep base) a a' →
      RuntimeCongruenceStep base (.sexp l (pre ++ a :: post)) (.sexp l (pre ++ a' :: post))
  | substB {b b' r : AST} {v : DottedPath} :
      ReflTransGen (RewStep base) b b' →
      RuntimeCongruenceStep base (.subst b r v) (.subst b' r v)
  | substR {b r r' : AST} {v : DottedPath} :
      ReflTransGen (RewStep base) r r' →
      RuntimeCongruenceStep base (.subst b r v) (.subst b r' v)

/-- Every runtime congruence schema step is already reachable in the base runtime closure. -/
theorem RuntimeCongruenceStep.reachable {base : Presentation} {t u : AST}
    (h : RuntimeCongruenceStep base t u) :
    ReflTransGen (RewStep base) t u := by
  cases h with
  | sexpArg hinner => exact rewStepMany_arg base hinner
  | substB hinner => exact rewStepMany_substB base hinner
  | substR hinner => exact rewStepMany_substR base hinner

/-- A relation extends `RewStep base` only by runtime congruence schemas. -/
def RuntimeCongruenceRelationExtension (base : Presentation) (rel : AST → AST → Prop) : Prop :=
  (∀ t u, RewStep base t u → rel t u) ∧
  ∀ t u, rel t u → RewStep base t u ∨ RuntimeCongruenceStep base t u

/-- A step of a runtime-congruence relation extension is reachable in the base closure. -/
theorem reachable_of_runtimeCongruenceRelationExtension {base : Presentation} {rel : AST → AST → Prop}
    (hext : RuntimeCongruenceRelationExtension base rel) {t u : AST} (h : rel t u) :
    ReflTransGen (RewStep base) t u := by
  rcases hext.2 t u h with hbase | hcong
  · exact ReflTransGen.single hbase
  · exact hcong.reachable

/-- Confluence transfers to a relation that extends the base only by runtime congruence schemas. -/
theorem confluent_of_runtimeCongruenceRelationExtension {base : Presentation} {rel : AST → AST → Prop}
    (hext : RuntimeCongruenceRelationExtension base rel) (hconf : Confluent (RewStep base)) :
    Confluent rel :=
  confluent_squeeze
    (fun _ _ h => hext.1 _ _ h)
    (fun _ _ h => reachable_of_runtimeCongruenceRelationExtension hext h)
    hconf

/-! ### Syntactic facts for one-premise `sexp` argument congruence rules -/

/-- Instantiate distributes through argument-list append. -/
theorem instList_append (bnds : List (String × AST)) :
    ∀ xs ys : List AST,
      AST.instList bnds (xs ++ ys) = AST.instList bnds xs ++ AST.instList bnds ys
  | [], _ => rfl
  | _ :: xs, ys => by
      simp only [List.cons_append, AST.instList, instList_append bnds xs ys]

/-- Subst-free argument lists are closed under append. -/
theorem substFreeList_append {xs ys : List AST}
    (hxs : SubstFreeList xs) (hys : SubstFreeList ys) : SubstFreeList (xs ++ ys) := by
  induction xs with
  | nil => exact hys
  | cons a xs ih =>
      simp only [List.cons_append, SubstFreeList] at hxs ⊢
      exact ⟨hxs.1, ih hxs.2⟩

/-- A fresh target binding does not change instantiation of patterns that do not mention it. -/
theorem instList_extend_fresh {tgt : String} {v : AST} {bnds : List (String × AST)}
    {ps : List AST} (hsf : SubstFreeList ps) (hfresh : tgt ∉ varsOfList ps) :
    AST.instList ((tgt, v) :: bnds) ps = AST.instList bnds ps := by
  apply instList_agree hsf
  intro x hx
  rw [bndLookup_cons_of_ne (t := v) (bnds0 := bnds) ?_]
  intro hxt
  subst hxt
  exact hfresh hx

/-- The left side of a single-premise argument congruence rule reconstructs the matched context. -/
theorem sexpArgCong_lhs_eq {src : String} {lab : Label} {prePat postPat : List AST}
    {t : AST} {bnds : List (String × AST)}
    (hsfpre : SubstFreeList prePat) (hsfpost : SubstFreeList postPat)
    (hm : AST.matchPat (.sexp lab (prePat ++ .var (.base src) :: postPat)) t [] = some bnds) :
    t = .sexp lab
      (AST.instList bnds prePat ++ AST.inst bnds (.var (.base src)) :: AST.instList bnds postPat) := by
  have hsfmid : SubstFreeList (.var (.base src) :: postPat) := by
    simp only [SubstFreeList, SubstFree]
    exact ⟨trivial, hsfpost⟩
  have hsfargs : SubstFreeList (prePat ++ .var (.base src) :: postPat) :=
    substFreeList_append hsfpre hsfmid
  have hinst :
      AST.inst bnds (.sexp lab (prePat ++ .var (.base src) :: postPat)) = t :=
    matchPat_inst_eq (by simpa [SubstFree] using hsfargs) hm
  rw [← hinst]
  simp only [AST.inst]
  rw [instList_append]
  simp only [AST.instList]
  rfl

/-- The right side of a single-premise argument congruence rule is the rebuilt target context. -/
theorem sexpArgCong_rhs_eq {tgt : String} {lab : Label} {prePat postPat : List AST}
    {bnds : List (String × AST)} {B : AST}
    (hsfpre : SubstFreeList prePat) (hsfpost : SubstFreeList postPat)
    (hfreshPre : tgt ∉ varsOfList prePat) (hfreshPost : tgt ∉ varsOfList postPat) :
    AST.inst ((tgt, B) :: bnds) (.sexp lab (prePat ++ .var (.base tgt) :: postPat))
      = .sexp lab (AST.instList bnds prePat ++ B :: AST.instList bnds postPat) := by
  simp only [AST.inst]
  rw [instList_append]
  simp only [AST.instList]
  rw [instList_extend_fresh (bnds := bnds) (v := B) hsfpre hfreshPre]
  rw [inst_var_of_bndLookup (bndLookup_cons_self tgt B bnds)]
  rw [instList_extend_fresh (bnds := bnds) (v := B) hsfpost hfreshPost]

/-- Instantiating a `Subst` RHS resolves the substitution rather than rebuilding a `Subst` context. -/
theorem substBody_rhs_inst_resolves {tgt : String} {B repl : AST} {v : DottedPath}
    {bnds : List (String × AST)} :
    AST.inst ((tgt, B) :: bnds) (.subst (.var (.base tgt)) repl v)
      = AST.subst1 (AST.instSubstTarget ((tgt, B) :: bnds) v)
        (AST.inst ((tgt, B) :: bnds) repl) B := by
  rw [inst_subst_eq]
  rw [inst_var_of_bndLookup (bndLookup_cons_self tgt B bnds)]

/-- Instantiating a replacement-position `Subst` RHS also resolves the substitution immediately. -/
theorem substRepl_rhs_inst_resolves {tgt : String} {B body : AST} {v : DottedPath}
    {bnds : List (String × AST)} :
    AST.inst ((tgt, B) :: bnds) (.subst body (.var (.base tgt)) v)
      = AST.subst1 (AST.instSubstTarget ((tgt, B) :: bnds) v)
        B (AST.inst ((tgt, B) :: bnds) body) := by
  rw [inst_subst_eq]
  rw [inst_var_of_bndLookup (bndLookup_cons_self tgt B bnds)]

/-! ### Rule predicates and closure squeeze for premised congruence extensions -/

/-- A rewrite declaration is a one-premise `sexp` argument congruence rule. -/
def SexpArgCongRule (rd : RewriteDecl) : Prop :=
  ∃ src tgt lab prePat postPat,
    rd.rw =
      .ctx ⟨.base src, .base tgt⟩
        (.base (.sexp lab (prePat ++ .var (.base src) :: postPat))
          (.sexp lab (prePat ++ .var (.base tgt) :: postPat))) ∧
    src ≠ tgt ∧ tgt ∉ varsOfList prePat ∧ tgt ∉ varsOfList postPat ∧
    SubstFreeList prePat ∧ SubstFreeList postPat

/-- The rho-calculus `new` congruence shape: `PNew[x, Src]` rewrites to `PNew[x, Tgt]`. -/
def rNewShapeCongRule : RewriteDecl :=
  { name := "RNew-shape"
    rw := .ctx ⟨.base "Src", .base "Tgt"⟩
      (.base
        (.sexp (.id "PNew") [.var (.base "x"), .var (.base "Src")])
        (.sexp (.id "PNew") [.var (.base "x"), .var (.base "Tgt")])) }

/-- `RNew`-style binder congruence is covered as a sexp argument congruence rule. -/
theorem rNewShapeCongRule_is_sexpArgCongRule : SexpArgCongRule rNewShapeCongRule := by
  refine ⟨"Src", "Tgt", .id "PNew", [.var (.base "x")], [], rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp [varsOfList, varsOf]
  · simp [varsOfList]
  · simp [SubstFreeList, SubstFree]
  · simp [SubstFreeList]

/-
True `AST.subst` nodes are not an extra syntactic case of `SexpArgCongRule`. A runtime rewrite fires
by instantiating its right-hand side with `AST.inst`, and `AST.inst` resolves `Subst` through
`AST.subst1`. So a rule shaped like `let src ~> tgt in Subst[src, r, v] ~> Subst[tgt, r, v]`
does not rebuild `Subst[B, r, v]`; it contracts to `subst1 v r B`. The conservative context closure
for actual `Subst` nodes therefore lives at the `RewStep.substB` and `RewStep.substR` layer, not as
another top-level presentation rule shape.
-/

/-- All top-level rules of a presentation are premise-free. -/
def PremiseFreeRewrites (p : Presentation) : Prop :=
  ∀ rd, rd ∈ p.rewrites → rd.rw.premises = []

/-- `full` extends a premise-free base presentation only by `sexp` argument congruence rules. -/
def SexpArgCongExtension (base full : Presentation) : Prop :=
  (∀ rd, rd ∈ base.rewrites → rd ∈ full.rewrites) ∧
  PremiseFreeRewrites base ∧
  ∀ rd, rd ∈ full.rewrites → rd ∈ base.rewrites ∨ SexpArgCongRule rd

mutual
  /-- Top-level reduction is monotone when every base rule is present in the larger presentation. -/
  theorem reduces_mono {base full : Presentation}
      (hsub : ∀ rd, rd ∈ base.rewrites → rd ∈ full.rewrites) :
      ∀ {t u : AST}, Reduces base t u → Reduces full t u
    | _, _, Reduces.step rd bnds bnds' hmem hm hph hu =>
        Reduces.step rd bnds bnds' (hsub rd hmem) hm (premisesHold_mono hsub hph) hu

  /-- Premise satisfaction is monotone under rewrite-list inclusion. -/
  theorem premisesHold_mono {base full : Presentation}
      (hsub : ∀ rd, rd ∈ base.rewrites → rd ∈ full.rewrites) :
      ∀ {hs : List Hyp} {bnds rest : List (String × AST)},
        PremisesHold base hs bnds rest → PremisesHold full hs bnds rest
    | _, _, _, PremisesHold.nil => PremisesHold.nil
    | _, _, _, PremisesHold.cons hred htail =>
        PremisesHold.cons (reduces_mono hsub hred) (premisesHold_mono hsub htail)
end

/-- `RewStep` is monotone when every base rewrite is present in the larger presentation. -/
theorem rewStep_mono {base full : Presentation}
    (hsub : ∀ rd, rd ∈ base.rewrites → rd ∈ full.rewrites) {t u : AST}
    (h : RewStep base t u) : RewStep full t u := by
  induction h with
  | top hred => exact RewStep.top (reduces_mono hsub hred)
  | arg hstep ih => exact RewStep.arg ih
  | substB hstep ih => exact RewStep.substB ih
  | substR hstep ih => exact RewStep.substR ih

/-- Every top-level step in a premised `sexp`-argument presentation extension is either a base step or
    an already-instantiated runtime congruence schema. -/
theorem reduces_base_or_runtimeCongruence_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) {t u : AST} (hred : Reduces full t u) :
    RewStep base t u ∨ RuntimeCongruenceStep base t u := by
  refine Reduces.rec (p := full)
    (motive_1 := fun t u _ => RewStep base t u ∨ RuntimeCongruenceStep base t u)
    (motive_2 := fun hs bnds rest _ =>
      ∀ {src tgt : String}, hs = [⟨.base src, .base tgt⟩] →
        ∃ B, rest = (tgt, B) :: bnds ∧
          ReflTransGen (RewStep base) (AST.inst bnds (.var (.base src))) B)
    ?step ?nil ?cons hred
  · intro t u rd bnds bnds' hmem hm hph hu hphIH
    rcases hext.2.2 rd hmem with hbase | hcong
    · have hprem : rd.rw.premises = [] := hext.2.1 rd hbase
      have hph0 : PremisesHold full [] bnds bnds' := by simpa [hprem] using hph
      cases hph0
      have hredBase : Reduces base t u := by
        refine Reduces.step rd bnds bnds hbase hm ?_ hu
        simpa [hprem] using (PremisesHold.nil : PremisesHold base [] bnds bnds)
      exact Or.inl (RewStep.top hredBase)
    · obtain ⟨src, tgt, lab, prePat, postPat, hrw, _hsrcne,
        hfreshPre, hfreshPost, hsfpre, hsfpost⟩ := hcong
      have hpremises : rd.rw.premises = [⟨.base src, .base tgt⟩] := by
        simp [hrw, Rewrite.premises]
      obtain ⟨B, hbnds', hinner⟩ := hphIH (src := src) (tgt := tgt) hpremises
      have hmctx :
          AST.matchPat (.sexp lab (prePat ++ .var (.base src) :: postPat)) t [] = some bnds := by
        simpa [hrw, Rewrite.conclusion] using hm
      have htctx :
          t = .sexp lab
            (AST.instList bnds prePat ++ AST.inst bnds (.var (.base src)) ::
              AST.instList bnds postPat) :=
        sexpArgCong_lhs_eq hsfpre hsfpost hmctx
      have huctx :
          u = .sexp lab (AST.instList bnds prePat ++ B :: AST.instList bnds postPat) := by
        rw [hu, hbnds']
        simpa [hrw, Rewrite.conclusion] using
          (sexpArgCong_rhs_eq (bnds := bnds) (B := B) hsfpre hsfpost hfreshPre hfreshPost)
      rw [htctx, huctx]
      exact Or.inr (RuntimeCongruenceStep.sexpArg hinner)
  · intro bnds src tgt hsingle
    cases hsingle
  · intro h hs bnds rest B hprem htail hpremIH htailIH src tgt hsingle
    cases hsingle
    cases htail
    refine ⟨B, rfl, ?_⟩
    rcases hpremIH with hbase | hcong
    · exact ReflTransGen.single hbase
    · exact hcong.reachable

/-- Every top-level step in a congruence extension is already reachable by base context steps. -/
theorem reduces_squeeze_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) {t u : AST} (hred : Reduces full t u) :
    ReflTransGen (RewStep base) t u := by
  rcases reduces_base_or_runtimeCongruence_of_sexpArgCongExtension hext hred with hbase | hcong
  · exact ReflTransGen.single hbase
  · exact hcong.reachable

/-- Every context step in a premised `sexp`-argument presentation extension is either a base step or an
    already-instantiated runtime congruence schema. Nested `Subst` contexts appear here directly. -/
theorem rewStep_base_or_runtimeCongruence_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) {t u : AST} (h : RewStep full t u) :
    RewStep base t u ∨ RuntimeCongruenceStep base t u := by
  induction h with
  | top hred => exact reduces_base_or_runtimeCongruence_of_sexpArgCongExtension hext hred
  | arg hstep ih =>
      right
      exact RuntimeCongruenceStep.sexpArg (by
        rcases ih with hbase | hcong
        · exact ReflTransGen.single hbase
        · exact hcong.reachable)
  | substB hstep ih =>
      right
      exact RuntimeCongruenceStep.substB (by
        rcases ih with hbase | hcong
        · exact ReflTransGen.single hbase
        · exact hcong.reachable)
  | substR hstep ih =>
      right
      exact RuntimeCongruenceStep.substR (by
        rcases ih with hbase | hcong
        · exact ReflTransGen.single hbase
        · exact hcong.reachable)

/-- The runtime relation of a premised `sexp`-argument presentation extension extends its base only by
    runtime congruence schemas. -/
theorem runtimeCongruenceRelationExtension_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) :
    RuntimeCongruenceRelationExtension base (RewStep full) := by
  constructor
  · intro t u h
    exact rewStep_mono hext.1 h
  · intro t u h
    exact rewStep_base_or_runtimeCongruence_of_sexpArgCongExtension hext h

/-- Every context step in a congruence extension is already reachable by base context steps. -/
theorem rewStep_squeeze_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) {t u : AST} (h : RewStep full t u) :
    ReflTransGen (RewStep base) t u :=
  reachable_of_runtimeCongruenceRelationExtension
    (runtimeCongruenceRelationExtension_of_sexpArgCongExtension hext) h

/-- A squeezed step also squeezes under the body of a `Subst` context. -/
theorem rewStep_squeeze_substB_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) {b b' r : AST} {v : DottedPath}
    (h : RewStep full b b') :
    ReflTransGen (RewStep base) (.subst b r v) (.subst b' r v) :=
  rewStepMany_substB base (rewStep_squeeze_of_sexpArgCongExtension hext h)

/-- A squeezed step also squeezes under the replacement of a `Subst` context. -/
theorem rewStep_squeeze_substR_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) {b r r' : AST} {v : DottedPath}
    (h : RewStep full r r') :
    ReflTransGen (RewStep base) (.subst b r v) (.subst b r' v) :=
  rewStepMany_substR base (rewStep_squeeze_of_sexpArgCongExtension hext h)

/-- A full congruence extension has the same reflexive-transitive closure as its base. -/
theorem reflTransGen_eq_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) :
    ∀ {a b : AST}, ReflTransGen (RewStep full) a b ↔ ReflTransGen (RewStep base) a b :=
  reflTransGen_eq_of_squeeze
    (fun _ _ h => rewStep_mono hext.1 h)
    (fun _ _ h => rewStep_squeeze_of_sexpArgCongExtension hext h)

/-- Global confluence transfers from a base presentation to its congruence extension. -/
theorem RewStep_confluent_of_sexpArgCongExtension {base full : Presentation}
    (hext : SexpArgCongExtension base full) (hconf : Confluent (RewStep base)) :
    Confluent (RewStep full) :=
  confluent_of_runtimeCongruenceRelationExtension
    (runtimeCongruenceRelationExtension_of_sexpArgCongExtension hext)
    hconf

/-- Conditional runtime bridge on the embedded first-order fragment. -/
theorem cong_RewStep_confluent_on_emb (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    {full : Presentation} (hext : SexpArgCongExtension (embPres ν R) full)
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf)
    (hconf : Confluent (Rstep R)) {s : FOTerm} {u1 u2 : AST}
    (h1 : ReflTransGen (RewStep full) (emb ν s) u1)
    (h2 : ReflTransGen (RewStep full) (emb ν s) u2) :
    Joinable (RewStep full) u1 u2 := by
  have heq : ∀ {a b : AST}, ReflTransGen (RewStep full) a b ↔
      ReflTransGen (RewStep (embPres ν R)) a b :=
    reflTransGen_eq_of_sexpArgCongExtension hext
  exact joinable_of_reflTransGen_eq heq
    (RewStep_confluent_on_emb ν hν hvars hconf (heq.mp h1) (heq.mp h2))

/-- A concrete congruence rule for the projection-system witness. -/
def projCongRule : RewriteDecl :=
  { name := "proj-cong"
    rw := .ctx ⟨.base "x", .base "y"⟩
      (.base (.sexp (.id "g") [.var (.base "x")]) (.sexp (.id "g") [.var (.base "y")])) }

/-- The projection system plus one concrete premised argument congruence rule. -/
def projCongPres : Presentation :=
  .mk [] [] [] ((embPres vname projSys).rewrites ++ [projCongRule]) []

/-- The concrete source term used by the projection congruence witness. -/
def projCongStart : AST :=
  emb vname (.app "g" [.app "f" [.app "a" []]])

/-- The concrete target term used by the projection congruence witness. -/
def projCongEnd : AST :=
  emb vname (.app "g" [.app "a" []])

/-- The embedded projection presentation has no premised base rules. -/
theorem embPres_premiseFree {R : List (FOTerm × FOTerm)} :
    PremiseFreeRewrites (embPres ν R) := by
  intro rd hrd
  simp only [embPres, Presentation.rewrites, List.mem_map] at hrd
  obtain ⟨⟨l, r⟩, _hmem, hrd⟩ := hrd
  subst hrd
  rfl

/-- The concrete projection congruence presentation satisfies the extension predicate. -/
theorem projCongExtension : SexpArgCongExtension (embPres vname projSys) projCongPres := by
  constructor
  · intro rd hrd
    change rd ∈ (embPres vname projSys).rewrites ++ [projCongRule]
    exact List.mem_append_left [projCongRule] hrd
  constructor
  · exact embPres_premiseFree (ν := vname)
  · intro rd hrd
    change rd ∈ (embPres vname projSys).rewrites ++ [projCongRule] at hrd
    rw [List.mem_append] at hrd
    rcases hrd with hbase | hsingle
    · exact Or.inl hbase
    · simp only [List.mem_singleton] at hsingle
      subst hsingle
      right
      refine ⟨"x", "y", .id "g", [], [], rfl, ?_, ?_, ?_, ?_, ?_⟩
      · decide
      · simp [varsOfList]
      · simp [varsOfList]
      · simp [SubstFreeList]
      · simp [SubstFreeList]

/-- The embedded projection rule reduces `f(a)` to `a` at the runtime top level. -/
theorem projSys_runtime_reduces_a :
    Reduces (embPres vname projSys)
      (emb vname (.app "f" [.app "a" []])) (emb vname (.app "a" [])) := by
  simpa [projSys, emb, embList, vname, AST.inst, AST.instList] using
    (reduces_base (embPres vname projSys)
      (embRule vname (.app "f" [.var 0]) (.var 0))
      (emb vname (.app "f" [.var 0])) (emb vname (.var 0))
      (emb vname (.app "f" [.app "a" []]))
      [(vname 0, emb vname (.app "a" []))]
      (embRule_mem vname (by simp [projSys]))
      rfl
      (by rfl))

/-- The concrete premised congruence rule genuinely fires at the root. -/
theorem projCongRule_fires :
    Reduces projCongPres projCongStart projCongEnd := by
  let a : AST := emb vname (.app "a" [])
  let fa : AST := emb vname (.app "f" [.app "a" []])
  have hinner : Reduces projCongPres fa a :=
    reduces_mono projCongExtension.1 (by simpa [a, fa] using projSys_runtime_reduces_a)
  change Reduces projCongPres (.sexp (.id "g") [fa]) (.sexp (.id "g") [a])
  refine Reduces.step projCongRule [("x", fa)] [("y", a), ("x", fa)] ?hmem ?hmatch ?hprem ?hrhs
  · change projCongRule ∈ (embPres vname projSys).rewrites ++ [projCongRule]
    exact List.mem_append_right (embPres vname projSys).rewrites (List.mem_singleton_self projCongRule)
  · rfl
  · exact PremisesHold.cons (by simpa [a, fa, AST.inst] using hinner) PremisesHold.nil
  · rfl

/-- The concrete fired congruence reduction is also a runtime context step. -/
theorem projCongRule_fires_rewStep :
    RewStep projCongPres projCongStart projCongEnd :=
  RewStep.top projCongRule_fires

/-- The headline bridge applies to the concrete projection congruence presentation. -/
theorem projCong_RewStep_confluent_on_emb {u1 u2 : AST}
    (h1 : ReflTransGen (RewStep projCongPres) projCongStart u1)
    (h2 : ReflTransGen (RewStep projCongPres) projCongStart u2) :
    Joinable (RewStep projCongPres) u1 u2 :=
  cong_RewStep_confluent_on_emb vname vname_injective projCongExtension
    hvars_projSys confluent_projSys h1 h2

end MeTTaIL.CP
