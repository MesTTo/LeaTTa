-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Runtime.Simulation
Layer: Runtime
Purpose: Relational bridge from the Cordial Miners presentation to the verified MeTTaIL runtime
  relation. The theorems here prove that each declared protocol rewrite is a genuine `RewStepModAC`
  step, that each decodable head redex maps to the matching coarse protocol step, and that each head
  redex is backward-sound up to decoded stutter. Every `TrecState.Step` has a runtime step whose target
  decodes to the coarse target. Reachability and coarse well-formedness then transfer for the runtime
  witness produced by the forward theorem.
Imports: CordialMiners.Runtime.Presentation, CordialMiners.Trec.Safety, MeTTaILProofs.DecEq,
  MeTTaILProofs.MatcherCorrect
Trusted boundary: none
Main exports: propose_head_modAC, order_head_modAC, qapprove_head_modAC, certify_head_modAC,
  finalize_head_modAC, finalLead_head_modAC, propose_head_decodes, order_head_decodes,
  qapprove_head_decodes, certify_head_decodes, finalize_head_decodes, finalLead_head_decodes,
  acOpCM_true_ne_cmOp, acOpCM_eq_state_or_inbox, noEmbeddedConfig_acEq_iff, runtimeConfigShape_acEq_iff,
  runtimeConfigShape_of_acEq, noEmbeddedConfig_not_rewStep, noEmbeddedConfig_not_rewStepModAC,
  runtimeConfigShape_rewStep_top, runtimeConfigShape_rewStepModAC_top,
  propose_head_backward, order_head_backward, derivedKind_head_backward,
  qapprove_head_backward, certify_head_backward, finalize_head_backward, finalLead_head_backward,
  runtime_root_step_backward, runtime_step_direct, runtime_step_backward_of_astToState_acEq,
  decodeListA_acEq_of_decoder_acEq, decodeFactA_acEq_of_decoders_acEq,
  decodeStateA_acEq_of_decoders_acEq, astToState_acEq_of_decoders_acEq,
  runtime_step_backward_of_decoders_acEq,
  event_forward_decode, event_forward_step, event_forward_stutter, event_inbox_mem_forward_stutter,
  runtime_step_stutter_of_inserted_fact_mem, derived_state_mem_forward_stutter,
  derived_step_forward_decode, derived_step_forward_step, derived_step_forward_stutter, RuntimeStepDecodesTo,
  RuntimeStepIsCoarseStep, RuntimeForwardComplete, RuntimeEventSound, RuntimeDerivedSound,
  RuntimeEventStutterSound, RuntimeDerivedStutterSound, RuntimeScopedBridge,
  trec_step_forward_decode, trec_step_forward_reachable, trec_step_forward_wf,
  scoped_runtime_bridge, propose_second_inbox_modAC
Open obligations: the modulo-AC backward theorem is generic for field decoders that respect runtime
  AC-equivalence. There is no theorem for completely arbitrary raw decoders, because such decoders can
  distinguish AC-equivalent ASTs.
-/
import CordialMiners.Runtime.Presentation
import CordialMiners.Trec.Safety
import MeTTaILProofs.DecEq
import MeTTaILProofs.MatcherCorrect

namespace CordialMiners.Runtime

open MeTTaIL
open MeTTaIL.AC

attribute [local simp] cmA inboxA stateA evProposeA evOrderPayloadA orderedPrefixPayloadA
  proposeA qApproveA certThreshA finalA finalLeaderA appA stateOp inboxOp cmOp consA cmNil symA

/-- The Cordial Miners state label is AC-enabled. -/
theorem acOpCM_state : acOpCM stateOp = true := by
  simp [acOpCM, stateOp, inboxOp]

/-- The Cordial Miners inbox label is AC-enabled. -/
theorem acOpCM_inbox : acOpCM inboxOp = true := by
  simp [acOpCM, stateOp, inboxOp]

/-- A syntactic runtime step is also a modulo-AC step, using reflexive AC witnesses. -/
theorem rewStepModAC_of_rewStep {t t' : AST} (h : RewStep cmPresentation t t') :
    RewStepModAC acOpCM cmPresentation t t' :=
  ⟨t, t', ACEq.refl t, h, ACEq.refl t'⟩

/-- AC-enabled Cordial Miners labels are collection labels, not the configuration label. -/
theorem acOpCM_true_ne_cmOp {l : Label} (h : acOpCM l = true) : l ≠ cmOp := by
  intro hl
  subst l
  simp [acOpCM, stateOp, inboxOp, cmOp] at h

/-- A Cordial Miners AC-enabled label is one of the two runtime collection labels. -/
theorem acOpCM_eq_state_or_inbox {l : Label} (h : acOpCM l = true) :
    l = stateOp ∨ l = inboxOp := by
  cases l with
  | id name =>
      simp [acOpCM, stateOp, inboxOp] at h
      rcases h with hstate | hinbox
      · subst name
        exact Or.inl rfl
      · subst name
        exact Or.inr rfl
  | wild => simp [acOpCM, stateOp, inboxOp] at h
  | listE _ => simp [acOpCM, stateOp, inboxOp] at h
  | listCons _ => simp [acOpCM, stateOp, inboxOp] at h
  | listOne _ => simp [acOpCM, stateOp, inboxOp] at h

/-- Replacing one AC-equivalent payload preserves the no-embedded-configuration list invariant. -/
theorem noEmbeddedConfigList_append_cons_iff {pre post : List AST} {a a' : AST}
    (h : NoEmbeddedConfig a ↔ NoEmbeddedConfig a') :
    NoEmbeddedConfigList (pre ++ a :: post) ↔ NoEmbeddedConfigList (pre ++ a' :: post) := by
  induction pre with
  | nil =>
      simp [NoEmbeddedConfigList, h]
  | cons _ _ ih =>
      simp [NoEmbeddedConfigList, ih]

/-- AC-equivalence preserves the no-embedded-configuration payload invariant. -/
theorem noEmbeddedConfig_acEq_iff {source target : AST}
    (h : ACEq acOpCM source target) :
    NoEmbeddedConfig source ↔ NoEmbeddedConfig target := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | comm hac =>
      simp [NoEmbeddedConfig, NoEmbeddedConfigList, and_assoc, and_comm]
  | assoc hac =>
      simp [NoEmbeddedConfig, NoEmbeddedConfigList]
      tauto
  | argCong pre post _ ih =>
      constructor
      · intro hs
        exact ⟨hs.1, (noEmbeddedConfigList_append_cons_iff ih).1 hs.2⟩
      · intro ht
        exact ⟨ht.1, (noEmbeddedConfigList_append_cons_iff ih).2 ht.2⟩
  | substCongB _ ih =>
      simp [NoEmbeddedConfig, ih]
  | substCongR _ ih =>
      simp [NoEmbeddedConfig, ih]

/-- Replacing one AC-equivalent argument preserves the runtime configuration shape test. -/
private theorem runtimeConfigShape_argCong_iff {l : Label} (pre : List AST) {a a' : AST}
    (post : List AST) (h : NoEmbeddedConfig a ↔ NoEmbeddedConfig a') :
    RuntimeConfigShape (.sexp l (pre ++ a :: post)) ↔
      RuntimeConfigShape (.sexp l (pre ++ a' :: post)) := by
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simp [RuntimeConfigShape]
      | cons _ postTail =>
          cases postTail with
          | nil =>
              simp [RuntimeConfigShape, h]
          | cons _ _ =>
              simp [RuntimeConfigShape]
  | cons _ preTail =>
      cases preTail with
      | nil =>
          cases post with
          | nil =>
              simp [RuntimeConfigShape, h]
          | cons _ _ =>
              simp [RuntimeConfigShape]
      | cons _ _ =>
          simp [RuntimeConfigShape]

/-- AC-equivalence preserves the top-level runtime configuration shape boundary. -/
theorem runtimeConfigShape_acEq_iff {source target : AST}
    (h : ACEq acOpCM source target) :
    RuntimeConfigShape source ↔ RuntimeConfigShape target := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | comm hac =>
      have hl := acOpCM_true_ne_cmOp hac
      simp [RuntimeConfigShape, cmOp]
      intro hcm
      exact (hl (by simpa [cmOp] using hcm)).elim
  | assoc hac =>
      have hl := acOpCM_true_ne_cmOp hac
      simp [RuntimeConfigShape, cmOp]
      intro hcm
      exact (hl (by simpa [cmOp] using hcm)).elim
  | argCong pre post h _ =>
      exact runtimeConfigShape_argCong_iff pre post (noEmbeddedConfig_acEq_iff h)
  | substCongB =>
      simp [RuntimeConfigShape]
  | substCongR =>
      simp [RuntimeConfigShape]

/-- Forward form of `runtimeConfigShape_acEq_iff`. -/
theorem runtimeConfigShape_of_acEq {source target : AST}
    (h : ACEq acOpCM source target) :
    RuntimeConfigShape source → RuntimeConfigShape target :=
  (runtimeConfigShape_acEq_iff h).1

/-- A clean payload cannot match a pattern rooted at `cm`. -/
private theorem noEmbeddedConfig_match_cmRoot_none (args : List AST) (source : AST)
    (bnds : List (String × AST)) (hclean : NoEmbeddedConfig source) :
    AST.matchPat (.sexp cmOp args) source bnds = none := by
  cases source with
  | var _ =>
      simp [AST.matchPat, cmOp]
  | sexp l termArgs =>
      rcases hclean with ⟨hl, _⟩
      simp [AST.matchPat, cmOp]
      intro hcm
      exact (hl (by simpa [cmOp] using hcm.symm)).elim
  | subst _ _ _ =>
      simp [AST.matchPat, cmOp]

/-- Every declared runtime rule has a `cm`-rooted left-hand side, so a clean payload has no top redex. -/
private theorem noEmbeddedConfig_not_reduces {source target : AST}
    (hclean : NoEmbeddedConfig source) :
    ¬ Reduces cmPresentation source target := by
  intro hred
  cases hred with
  | step rd bnds bnds' hmem hmatch _ _ =>
      simp [cmPresentation, Presentation.rewrites] at hmem
      rcases hmem with hrd | hrd | hrd | hrd | hrd | hrd
      all_goals
        subst rd
        simp [proposeRule, orderRule, finalLeadRule, finalizeRule, certifyRule, qapproveRule,
          baseDecl, Rewrite.conclusion] at hmatch
        have hbad : (none : Option (List (String × AST))) = some bnds :=
          (noEmbeddedConfig_match_cmRoot_none _ source [] hclean).symm.trans hmatch
        cases hbad

/-- The focused argument of a clean `sexp` argument list is clean. -/
private theorem noEmbeddedConfigList_append_cons_self {pre post : List AST} {a : AST} :
    NoEmbeddedConfigList (pre ++ a :: post) → NoEmbeddedConfig a := by
  induction pre with
  | nil =>
      intro h
      exact h.1
  | cons _ _ ih =>
      intro h
      exact ih h.2

/-- A clean payload has no Cordial Miners runtime rewrite step inside it. -/
theorem noEmbeddedConfig_not_rewStep {source target : AST}
    (hclean : NoEmbeddedConfig source) :
    ¬ RewStep cmPresentation source target := by
  intro hstep
  induction hstep with
  | top hred =>
      exact noEmbeddedConfig_not_reduces hclean hred
  | arg hstep ih =>
      exact ih (noEmbeddedConfigList_append_cons_self hclean.2)
  | substB hstep ih =>
      exact ih hclean.1
  | substR hstep ih =>
      exact ih hclean.2

/-- A clean payload has no Cordial Miners runtime rewrite step modulo AC. -/
theorem noEmbeddedConfig_not_rewStepModAC {source target : AST}
    (hclean : NoEmbeddedConfig source) :
    ¬ RewStepModAC acOpCM cmPresentation source target := by
  intro hstep
  rcases hstep with ⟨u, _, hsource, hrel, _⟩
  exact noEmbeddedConfig_not_rewStep ((noEmbeddedConfig_acEq_iff hsource).1 hclean) hrel

/-- The focused child of a shaped runtime configuration is a clean payload. -/
private theorem runtimeConfigShape_arg_clean {l : Label} {pre post : List AST} {a : AST}
    (hshape : RuntimeConfigShape (.sexp l (pre ++ a :: post))) :
    NoEmbeddedConfig a := by
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simp [RuntimeConfigShape] at hshape
      | cons _ postTail =>
          cases postTail with
          | nil =>
              exact hshape.2.1
          | cons _ _ =>
              simp [RuntimeConfigShape] at hshape
  | cons _ preTail =>
      cases preTail with
      | nil =>
          cases post with
          | nil =>
              exact hshape.2.2
          | cons _ _ =>
              simp [RuntimeConfigShape] at hshape
      | cons _ _ =>
          simp [RuntimeConfigShape] at hshape

/-- Any ordinary runtime step from a shaped configuration fires at the configuration root. -/
theorem runtimeConfigShape_rewStep_top {source target : AST}
    (hshape : RuntimeConfigShape source) (hstep : RewStep cmPresentation source target) :
    Reduces cmPresentation source target := by
  cases hstep with
  | top hred =>
      exact hred
  | arg hchild =>
      exact False.elim
        (noEmbeddedConfig_not_rewStep (runtimeConfigShape_arg_clean hshape) hchild)
  | substB =>
      simp [RuntimeConfigShape] at hshape
  | substR =>
      simp [RuntimeConfigShape] at hshape

/-- A modulo-AC runtime step from a shaped configuration chooses a shaped representative and then fires
    at that representative's root. -/
theorem runtimeConfigShape_rewStepModAC_top {source target : AST}
    (hshape : RuntimeConfigShape source) (hstep : RewStepModAC acOpCM cmPresentation source target) :
    ∃ u u',
      ACEq acOpCM source u ∧ RuntimeConfigShape u ∧
        Reduces cmPresentation u u' ∧ ACEq acOpCM u' target := by
  rcases hstep with ⟨u, u', hsource, hrel, htarget⟩
  have hshapeU : RuntimeConfigShape u := runtimeConfigShape_of_acEq hsource hshape
  exact ⟨u, u', hsource, hshapeU, runtimeConfigShape_rewStep_top hshapeU hrel, htarget⟩

/-- A proposal event at the head of the inbox fires the proposal rule. -/
theorem propose_head_modAC (w h ibrest st : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA (inboxA (evProposeA w h) ibrest) st)
      (cmA ibrest (stateA (proposeA w h) st)) := by
  apply rewStepModAC_of_rewStep
  exact RewStep.top
    (reduces_of_applyBaseRewrite cmPresentation proposeRule _ _
      (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

/-- An order event at the head of the inbox fires the order rule. -/
theorem order_head_modAC (payload ibrest st : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA (inboxA (evOrderPayloadA payload) ibrest) st)
      (cmA ibrest (stateA (orderedPrefixPayloadA payload) st)) := by
  apply rewStepModAC_of_rewStep
  exact RewStep.top
    (reduces_of_applyBaseRewrite cmPresentation orderRule _ _
      (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

/-- A proposal fact at the head of the state collection fires the quorum-approval rule. -/
theorem qapprove_head_modAC (w h ib rest : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA ib (stateA (proposeA w h) rest))
      (cmA ib (stateA (qApproveA w h) (stateA (proposeA w h) rest))) := by
  apply rewStepModAC_of_rewStep
  exact RewStep.top
    (reduces_of_applyBaseRewrite cmPresentation qapproveRule _ _
      (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

/-- A quorum-approval fact at the head of the state collection fires the certificate rule. -/
theorem certify_head_modAC (w h ib rest : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA ib (stateA (qApproveA w h) rest))
      (cmA ib (stateA (certThreshA w h) (stateA (qApproveA w h) rest))) := by
  apply rewStepModAC_of_rewStep
  exact RewStep.top
    (reduces_of_applyBaseRewrite cmPresentation certifyRule _ _
      (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

/-- A threshold-certificate fact at the head of the state collection fires the finality rule. -/
theorem finalize_head_modAC (w h ib rest : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA ib (stateA (certThreshA w h) rest))
      (cmA ib (stateA (finalA w h) (stateA (certThreshA w h) rest))) := by
  apply rewStepModAC_of_rewStep
  exact RewStep.top
    (reduces_of_applyBaseRewrite cmPresentation finalizeRule _ _
      (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

/-- A finality fact at the head of the state collection fires the final-leader rule. -/
theorem finalLead_head_modAC (w h ib rest : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA ib (stateA (finalA w h) rest))
      (cmA ib (stateA (finalLeaderA w h) (stateA (finalA w h) rest))) := by
  apply rewStepModAC_of_rewStep
  exact RewStep.top
      (reduces_of_applyBaseRewrite cmPresentation finalLeadRule _ _
        (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

/-- Shared decoding fact for derived rules whose LHS observes one state fact and whose RHS adds one
    derived fact while keeping the observed fact. -/
theorem derived_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    {ib rest src dst : AST} {srcFact dstFact : TrecFact Wave Hash}
    (hsrcFlat : collectA stateOp src = [src])
    (hdstFlat : collectA stateOp dst = [dst])
    (hsrc : decodeFactA dW dH src = some srcFact)
    (hdst : decodeFactA dW dH dst = some dstFact)
    (step : ∀ s : TrecState Wave Hash, srcFact ∈ s → TrecState.Step s (insert dstFact s)) :
    TrecState.Step
      (astToState dW dH (cmA ib (stateA src rest)))
      (astToState dW dH (cmA ib (stateA dst (stateA src rest)))) := by
  let s : TrecState Wave Hash := astToState dW dH (cmA ib (stateA src rest))
  have hsrcFlat' : collectA (Label.id "state") src = [src] := by
    simpa [stateOp] using hsrcFlat
  have hdstFlat' : collectA (Label.id "state") dst = [dst] := by
    simpa [stateOp] using hdstFlat
  have hpre : srcFact ∈ s := by
    simp [s, astToState, decodeStateA, collectA, hsrcFlat', hsrc]
  simpa [s, astToState, decodeStateA, collectA, hsrcFlat', hdstFlat', hsrc, hdst] using
    step s hpre

/-- The four derived Cordial Miners rules share the same runtime shape. -/
inductive DerivedKind where
  | qapprove
  | certify
  | finalize
  | finalLead

namespace DerivedKind

/-- The precondition fact matched by a derived rule. -/
def srcA : DerivedKind → AST → AST → AST
  | qapprove, w, h => proposeA w h
  | certify, w, h => qApproveA w h
  | finalize, w, h => certThreshA w h
  | finalLead, w, h => finalA w h

/-- The fact inserted by a derived rule. -/
def dstA : DerivedKind → AST → AST → AST
  | qapprove, w, h => qApproveA w h
  | certify, w, h => certThreshA w h
  | finalize, w, h => finalA w h
  | finalLead, w, h => finalLeaderA w h

/-- The decoded precondition fact for a derived rule. -/
def srcFact {Wave Hash : Type*} : DerivedKind → Wave → Hash → TrecFact Wave Hash
  | qapprove, w, h => TrecFact.propose w h
  | certify, w, h => TrecFact.qApprove w h
  | finalize, w, h => TrecFact.certThresh w h
  | finalLead, w, h => TrecFact.final w h

/-- The decoded inserted fact for a derived rule. -/
def dstFact {Wave Hash : Type*} : DerivedKind → Wave → Hash → TrecFact Wave Hash
  | qapprove, w, h => TrecFact.qApprove w h
  | certify, w, h => TrecFact.certThresh w h
  | finalize, w, h => TrecFact.final w h
  | finalLead, w, h => TrecFact.finalLeader w h

/-- Select the source or destination side of a derived rule. -/
inductive Side where
  | src
  | dst

/-- The AST fact on one side of a derived rule. -/
def sideA : Side → DerivedKind → AST → AST → AST
  | .src, k, w, h => srcA k w h
  | .dst, k, w, h => dstA k w h

/-- The decoded coarse fact on one side of a derived rule. -/
def sideFact {Wave Hash : Type*} : Side → DerivedKind → Wave → Hash → TrecFact Wave Hash
  | .src, k, w, h => srcFact k w h
  | .dst, k, w, h => dstFact k w h

/-- Derived-rule side ASTs are leaves of the state AC collection. -/
theorem sideFlat (side : Side) (k : DerivedKind) (w h : AST) :
    collectA stateOp (sideA side k w h) = [sideA side k w h] := by
  cases side <;> cases k <;> simp [sideA, srcA, dstA, collectA]

/-- Decoding either side AST recovers the corresponding coarse fact. -/
theorem decodeSide {Wave Hash : Type*} (side : Side) (k : DerivedKind)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    {w h : AST} {w' : Wave} {h' : Hash} (hw : dW w = some w') (hh : dH h = some h') :
    decodeFactA dW dH (sideA side k w h) = some (sideFact side k w' h') := by
  cases side <;> cases k <;>
    simp [sideA, sideFact, srcA, dstA, srcFact, dstFact, decodeFactA, decodePairA, hw, hh]

/-- The decoded coarse step for a derived rule. -/
theorem step {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (s : TrecState Wave Hash) (w : Wave) (h : Hash)
    (hpre : srcFact k w h ∈ s) : TrecState.Step s (insert (dstFact k w h) s) := by
  cases k <;> simp [srcFact, dstFact] at hpre ⊢
  · exact TrecState.Step.qapprove s w h hpre
  · exact TrecState.Step.certify s w h hpre
  · exact TrecState.Step.finalize s w h hpre
  · exact TrecState.Step.finalLead s w h hpre

end DerivedKind

/-- Any derived Cordial Miners head redex decodes to its corresponding coarse step. -/
theorem derivedKind_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (dW : AST → Option Wave) (dH : AST → Option Hash)
    {w h ib rest : AST} {w' : Wave} {h' : Hash}
    (hw : dW w = some w') (hh : dH h = some h') :
    TrecState.Step
      (astToState dW dH (cmA ib (stateA (DerivedKind.srcA k w h) rest)))
      (astToState dW dH
        (cmA ib (stateA (DerivedKind.dstA k w h) (stateA (DerivedKind.srcA k w h) rest)))) :=
  derived_head_decodes dW dH (DerivedKind.sideFlat .src k w h) (DerivedKind.sideFlat .dst k w h)
    (DerivedKind.decodeSide .src k dW dH hw hh) (DerivedKind.decodeSide .dst k dW dH hw hh)
    (fun s hpre => DerivedKind.step k s w' h' hpre)

/-- A decoded derived-rule target is a real coarse derived step. -/
theorem derived_step_of_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (dW : AST → Option Wave) (dH : AST → Option Hash)
    {s : TrecState Wave Hash} {w : Wave} {h : Hash} {target : AST}
    (hpre : DerivedKind.srcFact k w h ∈ s)
    (hdecode : astToState dW dH target = insert (DerivedKind.dstFact k w h) s) :
    TrecState.Step s (astToState dW dH target) := by
  rw [hdecode]
  exact DerivedKind.step k s w h hpre

/-- A proposal head redex decodes to the coarse proposal step. -/
theorem propose_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {w h ibrest st : AST} {w' : Wave} {h' : Hash}
    (hw : dW w = some w') (hh : dH h = some h') :
    TrecState.Step (astToState dW dH (cmA (inboxA (evProposeA w h) ibrest) st))
      (astToState dW dH (cmA ibrest (stateA (proposeA w h) st))) := by
  simpa [astToState, decodeStateA, collectA, cmA, stateA, proposeA, appA, stateOp, decodeFactA,
    decodePairA, hw, hh] using
      TrecState.Step.propose (decodeStateA dW dH st) w' h'

/-- An order head redex decodes to the coarse ordering step. -/
theorem order_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {payload ibrest st : AST} {hs : List Hash}
    (hp : decodeOrderedPayloadA dH [payload] = some hs) :
    TrecState.Step (astToState dW dH (cmA (inboxA (evOrderPayloadA payload) ibrest) st))
      (astToState dW dH (cmA ibrest (stateA (orderedPrefixPayloadA payload) st))) := by
  simpa [astToState, decodeStateA, collectA, cmA, stateA, orderedPrefixPayloadA, appA, stateOp,
    decodeFactA, hp] using
      TrecState.Step.order (decodeStateA dW dH st) hs

/-- Adding a state-collection leaf that does not decode is a decoded stutter. -/
theorem decodeStateA_stateA_none {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    {fact rest : AST} (hflat : collectA stateOp fact = [fact])
    (hdecode : decodeFactA dW dH fact = none) :
    decodeStateA dW dH (stateA fact rest) = decodeStateA dW dH rest := by
  unfold decodeStateA
  rw [show collectA stateOp (stateA fact rest) = collectA stateOp fact ++ collectA stateOp rest from rfl]
  rw [hflat, List.filterMap_append]
  simp [hdecode]

/-- A proposal head redex decodes to a coarse proposal step, or stutters if the event payload is
    undecodable. -/
theorem propose_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (w h ibrest st : AST) :
    TrecState.Step (astToState dW dH (cmA (inboxA (evProposeA w h) ibrest) st))
        (astToState dW dH (cmA ibrest (stateA (proposeA w h) st))) ∨
      astToState dW dH (cmA (inboxA (evProposeA w h) ibrest) st) =
        astToState dW dH (cmA ibrest (stateA (proposeA w h) st)) := by
  cases hw : dW w with
  | none =>
      right
      have hnone : decodeFactA dW dH (proposeA w h) = none := by
        simp [proposeA, appA, decodeFactA, decodePairA, hw]
      have hstutter := decodeStateA_stateA_none dW dH
        (fact := proposeA w h) (rest := st) (by simp [proposeA, appA, collectA]) hnone
      simpa [astToState, cmA, cmOp] using hstutter.symm
  | some _ =>
      cases hh : dH h with
      | none =>
          right
          have hnone : decodeFactA dW dH (proposeA w h) = none := by
            simp [proposeA, appA, decodeFactA, decodePairA, hw, hh]
          have hstutter := decodeStateA_stateA_none dW dH
            (fact := proposeA w h) (rest := st) (by simp [proposeA, appA, collectA]) hnone
          simpa [astToState, cmA, cmOp] using hstutter.symm
      | some _ =>
          exact Or.inl (propose_head_decodes dW dH hw hh)

/-- An order head redex decodes to a coarse ordering step, or stutters if the payload is undecodable. -/
theorem order_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (payload ibrest st : AST) :
    TrecState.Step (astToState dW dH (cmA (inboxA (evOrderPayloadA payload) ibrest) st))
        (astToState dW dH (cmA ibrest (stateA (orderedPrefixPayloadA payload) st))) ∨
      astToState dW dH (cmA (inboxA (evOrderPayloadA payload) ibrest) st) =
        astToState dW dH (cmA ibrest (stateA (orderedPrefixPayloadA payload) st)) := by
  cases hp : decodeOrderedPayloadA dH [payload] with
  | none =>
      right
      have hnone : decodeFactA dW dH (orderedPrefixPayloadA payload) = none := by
        simp [orderedPrefixPayloadA, appA, decodeFactA, hp]
      have hstutter := decodeStateA_stateA_none dW dH
        (fact := orderedPrefixPayloadA payload) (rest := st)
        (by simp [orderedPrefixPayloadA, appA, collectA]) hnone
      simpa [astToState, cmA, cmOp] using hstutter.symm
  | some _ =>
      exact Or.inl (order_head_decodes dW dH hp)

/-- A quorum-approval head redex decodes to the coarse quorum-approval step. -/
theorem qapprove_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {w h ib rest : AST}
    {w' : Wave} {h' : Hash} (hw : dW w = some w') (hh : dH h = some h') :
    TrecState.Step (astToState dW dH (cmA ib (stateA (proposeA w h) rest)))
      (astToState dW dH (cmA ib (stateA (qApproveA w h) (stateA (proposeA w h) rest)))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_decodes DerivedKind.qapprove dW dH (ib := ib) (rest := rest) hw hh

/-- A certificate head redex decodes to the coarse certificate step. -/
theorem certify_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {w h ib rest : AST}
    {w' : Wave} {h' : Hash} (hw : dW w = some w') (hh : dH h = some h') :
    TrecState.Step (astToState dW dH (cmA ib (stateA (qApproveA w h) rest)))
      (astToState dW dH (cmA ib (stateA (certThreshA w h) (stateA (qApproveA w h) rest)))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_decodes DerivedKind.certify dW dH (ib := ib) (rest := rest) hw hh

/-- A finality head redex decodes to the coarse finality step. -/
theorem finalize_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {w h ib rest : AST}
    {w' : Wave} {h' : Hash} (hw : dW w = some w') (hh : dH h = some h') :
    TrecState.Step (astToState dW dH (cmA ib (stateA (certThreshA w h) rest)))
      (astToState dW dH (cmA ib (stateA (finalA w h) (stateA (certThreshA w h) rest)))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_decodes DerivedKind.finalize dW dH (ib := ib) (rest := rest) hw hh

/-- A final-leader head redex decodes to the coarse final-leader step. -/
theorem finalLead_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {w h ib rest : AST}
    {w' : Wave} {h' : Hash} (hw : dW w = some w') (hh : dH h = some h') :
    TrecState.Step (astToState dW dH (cmA ib (stateA (finalA w h) rest)))
      (astToState dW dH (cmA ib (stateA (finalLeaderA w h) (stateA (finalA w h) rest)))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_decodes DerivedKind.finalLead dW dH (ib := ib) (rest := rest) hw hh

/-- A derived-rule head redex decodes to a coarse derived step, or stutters if its fields are
    undecodable. -/
theorem derivedKind_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (w h ib rest : AST) :
    TrecState.Step
        (astToState dW dH (cmA ib (stateA (DerivedKind.srcA k w h) rest)))
        (astToState dW dH
          (cmA ib (stateA (DerivedKind.dstA k w h) (stateA (DerivedKind.srcA k w h) rest)))) ∨
      astToState dW dH (cmA ib (stateA (DerivedKind.srcA k w h) rest)) =
        astToState dW dH
          (cmA ib (stateA (DerivedKind.dstA k w h) (stateA (DerivedKind.srcA k w h) rest))) := by
  cases hw : dW w with
  | none =>
      right
      have hdstNone : decodeFactA dW dH (DerivedKind.dstA k w h) = none := by
        cases k <;> simp [DerivedKind.dstA, qApproveA, certThreshA, finalA, finalLeaderA,
          appA, decodeFactA, decodePairA, hw]
      have hdstStutter := decodeStateA_stateA_none dW dH
        (fact := DerivedKind.dstA k w h) (rest := stateA (DerivedKind.srcA k w h) rest)
        (DerivedKind.sideFlat .dst k w h) hdstNone
      simpa [astToState, cmA, cmOp] using hdstStutter.symm
  | some _ =>
      cases hh : dH h with
      | none =>
          right
          have hdstNone : decodeFactA dW dH (DerivedKind.dstA k w h) = none := by
            cases k <;> simp [DerivedKind.dstA, qApproveA, certThreshA, finalA, finalLeaderA,
              appA, decodeFactA, decodePairA, hw, hh]
          have hdstStutter := decodeStateA_stateA_none dW dH
            (fact := DerivedKind.dstA k w h) (rest := stateA (DerivedKind.srcA k w h) rest)
            (DerivedKind.sideFlat .dst k w h) hdstNone
          simpa [astToState, cmA, cmOp] using hdstStutter.symm
      | some _ =>
          exact Or.inl (derivedKind_head_decodes k dW dH (ib := ib) (rest := rest) hw hh)

/-- A quorum-approval head redex is backward-sound up to decoded stutter. -/
theorem qapprove_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (w h ib rest : AST) :
    TrecState.Step (astToState dW dH (cmA ib (stateA (proposeA w h) rest)))
        (astToState dW dH (cmA ib (stateA (qApproveA w h) (stateA (proposeA w h) rest)))) ∨
      astToState dW dH (cmA ib (stateA (proposeA w h) rest)) =
        astToState dW dH (cmA ib (stateA (qApproveA w h) (stateA (proposeA w h) rest))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_backward DerivedKind.qapprove dW dH w h ib rest

/-- A certificate head redex is backward-sound up to decoded stutter. -/
theorem certify_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (w h ib rest : AST) :
    TrecState.Step (astToState dW dH (cmA ib (stateA (qApproveA w h) rest)))
        (astToState dW dH (cmA ib (stateA (certThreshA w h) (stateA (qApproveA w h) rest)))) ∨
      astToState dW dH (cmA ib (stateA (qApproveA w h) rest)) =
        astToState dW dH (cmA ib (stateA (certThreshA w h) (stateA (qApproveA w h) rest))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_backward DerivedKind.certify dW dH w h ib rest

/-- A finality head redex is backward-sound up to decoded stutter. -/
theorem finalize_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (w h ib rest : AST) :
    TrecState.Step (astToState dW dH (cmA ib (stateA (certThreshA w h) rest)))
        (astToState dW dH (cmA ib (stateA (finalA w h) (stateA (certThreshA w h) rest)))) ∨
      astToState dW dH (cmA ib (stateA (certThreshA w h) rest)) =
        astToState dW dH (cmA ib (stateA (finalA w h) (stateA (certThreshA w h) rest))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_backward DerivedKind.finalize dW dH w h ib rest

/-- A final-leader head redex is backward-sound up to decoded stutter. -/
theorem finalLead_head_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (w h ib rest : AST) :
    TrecState.Step (astToState dW dH (cmA ib (stateA (finalA w h) rest)))
        (astToState dW dH (cmA ib (stateA (finalLeaderA w h) (stateA (finalA w h) rest)))) ∨
      astToState dW dH (cmA ib (stateA (finalA w h) rest)) =
        astToState dW dH (cmA ib (stateA (finalLeaderA w h) (stateA (finalA w h) rest))) := by
  simpa [DerivedKind.srcA, DerivedKind.dstA] using
    derivedKind_head_backward DerivedKind.finalLead dW dH w h ib rest

/-- A direct root reduction by the Cordial Miners presentation decodes to a coarse step or to a
    decoded stutter. -/
theorem runtime_root_step_backward {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {source target : AST}
    (hred : Reduces cmPresentation source target) :
    TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
      astToState dW dH source = astToState dW dH target := by
  cases hred with
  | step rd bnds bnds' hmem hmatch hprem htarget =>
      simp [cmPresentation, Presentation.rewrites] at hmem
      rcases hmem with hrd | hrd | hrd | hrd | hrd | hrd
      · subst rd
        cases hprem
        have hsource : source =
            cmA
              (inboxA (evProposeA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (AST.inst bnds ibRestVar))
              (AST.inst bnds stVar) := by
          have hinst := matchPat_inst_eq
            (by simp [proposeRule, baseDecl, Rewrite.conclusion, SubstFree, SubstFreeList, cmA, inboxA,
              evProposeA, appA, wVar, hVar, ibRestVar, stVar, vA]) hmatch
          simpa [proposeRule, baseDecl, Rewrite.conclusion, cmA, inboxA, evProposeA, appA,
            wVar, hVar, ibRestVar, stVar, AST.inst, AST.instList] using hinst.symm
        have htarget' : target =
            cmA (AST.inst bnds ibRestVar)
              (stateA (proposeA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (AST.inst bnds stVar)) := by
          simpa [proposeRule, baseDecl, Rewrite.conclusion, cmA, stateA, proposeA, appA,
            wVar, hVar, ibRestVar, stVar, AST.inst, AST.instList] using htarget
        simpa [hsource, htarget'] using
          propose_head_backward dW dH (AST.inst bnds wVar) (AST.inst bnds hVar)
            (AST.inst bnds ibRestVar) (AST.inst bnds stVar)
      · subst rd
        cases hprem
        have hsource : source =
            cmA
              (inboxA (evOrderPayloadA (AST.inst bnds hsVar)) (AST.inst bnds ibRestVar))
              (AST.inst bnds stVar) := by
          have hinst := matchPat_inst_eq
            (by simp [orderRule, baseDecl, Rewrite.conclusion, SubstFree, SubstFreeList, cmA, inboxA,
              evOrderPayloadA, appA, hsVar, ibRestVar, stVar, vA]) hmatch
          simpa [orderRule, baseDecl, Rewrite.conclusion, cmA, inboxA, evOrderPayloadA, appA,
            hsVar, ibRestVar, stVar, AST.inst, AST.instList] using hinst.symm
        have htarget' : target =
            cmA (AST.inst bnds ibRestVar)
              (stateA (orderedPrefixPayloadA (AST.inst bnds hsVar)) (AST.inst bnds stVar)) := by
          simpa [orderRule, baseDecl, Rewrite.conclusion, cmA, stateA, orderedPrefixPayloadA,
            appA, hsVar, ibRestVar, stVar, AST.inst, AST.instList] using htarget
        simpa [hsource, htarget'] using
          order_head_backward dW dH (AST.inst bnds hsVar) (AST.inst bnds ibRestVar)
            (AST.inst bnds stVar)
      · subst rd
        cases hprem
        have hsource : source =
            cmA (AST.inst bnds ibVar)
              (stateA (finalA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (AST.inst bnds restVar)) := by
          have hinst := matchPat_inst_eq
            (by simp [finalLeadRule, baseDecl, Rewrite.conclusion, SubstFree, SubstFreeList, cmA, stateA,
              finalA, appA, wVar, hVar, ibVar, restVar, vA]) hmatch
          simpa [finalLeadRule, baseDecl, Rewrite.conclusion, cmA, stateA, finalA, appA,
            wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using hinst.symm
        have htarget' : target =
            cmA (AST.inst bnds ibVar)
              (stateA (finalLeaderA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (stateA (finalA (AST.inst bnds wVar) (AST.inst bnds hVar))
                  (AST.inst bnds restVar))) := by
          simpa [finalLeadRule, baseDecl, Rewrite.conclusion, cmA, stateA, finalA, finalLeaderA,
            appA, wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using htarget
        simpa [hsource, htarget'] using
          finalLead_head_backward dW dH (AST.inst bnds wVar) (AST.inst bnds hVar)
            (AST.inst bnds ibVar) (AST.inst bnds restVar)
      · subst rd
        cases hprem
        have hsource : source =
            cmA (AST.inst bnds ibVar)
              (stateA (certThreshA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (AST.inst bnds restVar)) := by
          have hinst := matchPat_inst_eq
            (by simp [finalizeRule, baseDecl, Rewrite.conclusion, SubstFree, SubstFreeList, cmA, stateA,
              certThreshA, appA, wVar, hVar, ibVar, restVar, vA]) hmatch
          simpa [finalizeRule, baseDecl, Rewrite.conclusion, cmA, stateA, certThreshA, appA,
            wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using hinst.symm
        have htarget' : target =
            cmA (AST.inst bnds ibVar)
              (stateA (finalA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (stateA (certThreshA (AST.inst bnds wVar) (AST.inst bnds hVar))
                  (AST.inst bnds restVar))) := by
          simpa [finalizeRule, baseDecl, Rewrite.conclusion, cmA, stateA, certThreshA, finalA,
            appA, wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using htarget
        simpa [hsource, htarget'] using
          finalize_head_backward dW dH (AST.inst bnds wVar) (AST.inst bnds hVar)
            (AST.inst bnds ibVar) (AST.inst bnds restVar)
      · subst rd
        cases hprem
        have hsource : source =
            cmA (AST.inst bnds ibVar)
              (stateA (qApproveA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (AST.inst bnds restVar)) := by
          have hinst := matchPat_inst_eq
            (by simp [certifyRule, baseDecl, Rewrite.conclusion, SubstFree, SubstFreeList, cmA, stateA,
              qApproveA, appA, wVar, hVar, ibVar, restVar, vA]) hmatch
          simpa [certifyRule, baseDecl, Rewrite.conclusion, cmA, stateA, qApproveA, appA,
            wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using hinst.symm
        have htarget' : target =
            cmA (AST.inst bnds ibVar)
              (stateA (certThreshA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (stateA (qApproveA (AST.inst bnds wVar) (AST.inst bnds hVar))
                  (AST.inst bnds restVar))) := by
          simpa [certifyRule, baseDecl, Rewrite.conclusion, cmA, stateA, qApproveA, certThreshA,
            appA, wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using htarget
        simpa [hsource, htarget'] using
          certify_head_backward dW dH (AST.inst bnds wVar) (AST.inst bnds hVar)
            (AST.inst bnds ibVar) (AST.inst bnds restVar)
      · subst rd
        cases hprem
        have hsource : source =
            cmA (AST.inst bnds ibVar)
              (stateA (proposeA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (AST.inst bnds restVar)) := by
          have hinst := matchPat_inst_eq
            (by simp [qapproveRule, baseDecl, Rewrite.conclusion, SubstFree, SubstFreeList, cmA, stateA,
              proposeA, appA, wVar, hVar, ibVar, restVar, vA]) hmatch
          simpa [qapproveRule, baseDecl, Rewrite.conclusion, cmA, stateA, proposeA, appA,
            wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using hinst.symm
        have htarget' : target =
            cmA (AST.inst bnds ibVar)
              (stateA (qApproveA (AST.inst bnds wVar) (AST.inst bnds hVar))
                (stateA (proposeA (AST.inst bnds wVar) (AST.inst bnds hVar))
                  (AST.inst bnds restVar))) := by
          simpa [qapproveRule, baseDecl, Rewrite.conclusion, cmA, stateA, proposeA, qApproveA,
            appA, wVar, hVar, ibVar, restVar, AST.inst, AST.instList] using htarget
        simpa [hsource, htarget'] using
          qapprove_head_backward dW dH (AST.inst bnds wVar) (AST.inst bnds hVar)
            (AST.inst bnds ibVar) (AST.inst bnds restVar)

/-- A direct contextual runtime step from a shaped configuration decodes to a coarse step or stutter.
    The shape invariant rules out every strict-subterm protocol redex. -/
theorem runtime_step_direct {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) {source target : AST}
    (hshape : RuntimeConfigShape source) (hstep : RewStep cmPresentation source target) :
    TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
      astToState dW dH source = astToState dW dH target :=
  runtime_root_step_backward dW dH (runtimeConfigShape_rewStep_top hshape hstep)

/-- A modulo-AC runtime step from a shaped configuration decodes to a coarse step or stutter whenever
    the selected decoder is invariant under the runtime AC equivalence. -/
theorem runtime_step_backward_of_astToState_acEq {Wave Hash : Type*} [DecidableEq Wave]
    [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hAC : ∀ {a b : AST}, ACEq acOpCM a b → astToState dW dH a = astToState dW dH b)
    {source target : AST}
    (hshape : RuntimeConfigShape source) (hstep : RewStepModAC acOpCM cmPresentation source target) :
    TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
      astToState dW dH source = astToState dW dH target := by
  rcases runtimeConfigShape_rewStepModAC_top hshape hstep with
    ⟨u, u', hsource, _, hred, htarget⟩
  have hsrc : astToState dW dH source = astToState dW dH u := hAC hsource
  have htgt : astToState dW dH u' = astToState dW dH target := hAC htarget
  rcases runtime_root_step_backward dW dH hred with hcoarse | hstutter
  · left
    rw [hsrc, ← htgt]
    exact hcoarse
  · right
    exact hsrc.trans (hstutter.trans htgt)

/-- List decoding respects runtime AC-equivalence when the element decoder does. -/
theorem decodeListA_acEq_of_decoder_acEq {α : Type*} (d : AST → Option α)
    (hd : ∀ {a b : AST}, ACEq acOpCM a b → d a = d b) {a b : AST}
    (h : ACEq acOpCM a b) :
    decodeListA d a = decodeListA d b := by
  induction h with
  | refl _ | substCongB | substCongR => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @comm l a b hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl <;> rfl
  | @assoc l a b c hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl <;> rfl
  | @argCong l pre a a' post h ih =>
      cases l with
      | id name =>
          cases pre with
          | nil =>
              cases post with
              | nil => simp [decodeListA]
              | cons _ postTail =>
                  cases postTail with
                  | nil =>
                      by_cases hname : name = "list-cons"
                      · subst name
                        simp [decodeListA, hd h]
                      · simp [decodeListA, hname]
                  | cons _ _ => simp [decodeListA]
          | cons _ preTail =>
              cases preTail with
              | nil =>
                  cases post with
                  | nil =>
                      by_cases hname : name = "list-cons"
                      · subst name
                        simp [decodeListA, ih]
                      · simp [decodeListA, hname]
                  | cons _ _ => simp [decodeListA]
              | cons _ _ => simp [decodeListA]
      | wild => cases pre <;> simp [decodeListA]
      | listE _ => cases pre <;> simp [decodeListA]
      | listCons _ => cases pre <;> simp [decodeListA]
      | listOne _ => cases pre <;> simp [decodeListA]

private theorem option_bind_single_eq {α : Type*} {x y : Option α} (h : x = y) :
    (x.bind fun z => some [z]) = (y.bind fun z => some [z]) := by
  rw [h]

private theorem decodeOrderedPayloadA_single_acEq_of_decoder_acEq {α : Type*}
    (d : AST → Option α) (hd : ∀ {a b : AST}, ACEq acOpCM a b → d a = d b)
    {a b : AST} (h : ACEq acOpCM a b) :
    decodeOrderedPayloadA d [a] = decodeOrderedPayloadA d [b] := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @comm l a b hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl
      · simpa [decodeOrderedPayloadA, decodeListA, stateOp] using
          option_bind_single_eq (hd (ACEq.comm (acOp := acOpCM) (l := stateOp) hac))
      · simpa [decodeOrderedPayloadA, decodeListA, inboxOp] using
          option_bind_single_eq (hd (ACEq.comm (acOp := acOpCM) (l := inboxOp) hac))
  | @assoc l a b c hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl
      · simpa [decodeOrderedPayloadA, decodeListA, stateOp] using
          option_bind_single_eq (hd (ACEq.assoc (acOp := acOpCM) (l := stateOp) hac))
      · simpa [decodeOrderedPayloadA, decodeListA, inboxOp] using
          option_bind_single_eq (hd (ACEq.assoc (acOp := acOpCM) (l := inboxOp) hac))
  | @argCong l pre a a' post h ih =>
      cases l with
      | id name =>
          by_cases hcons : name = "list-cons"
          · subst name
            cases pre with
            | nil =>
                cases post with
                | nil =>
                    simpa [decodeOrderedPayloadA, decodeListA] using
                      option_bind_single_eq
                        (hd (ACEq.argCong (acOp := acOpCM) (l := Label.id "list-cons") [] [] h))
                | cons p postTail =>
                    cases postTail with
                    | nil =>
                        simpa [decodeOrderedPayloadA, listConsA, appA] using
                          decodeListA_acEq_of_decoder_acEq d hd
                            (ACEq.argCong (acOp := acOpCM) (l := Label.id "list-cons") [] [p] h)
                    | cons q qs =>
                        simpa [decodeOrderedPayloadA] using
                          option_bind_single_eq
                            (hd (ACEq.argCong (acOp := acOpCM) (l := Label.id "list-cons")
                              [] (p :: q :: qs) h))
            | cons p preTail =>
                cases preTail with
                | nil =>
                    cases post with
                    | nil =>
                        simpa [decodeOrderedPayloadA, listConsA, appA] using
                          decodeListA_acEq_of_decoder_acEq d hd
                            (ACEq.argCong (acOp := acOpCM) (l := Label.id "list-cons") [p] [] h)
                    | cons q qs =>
                        simpa [decodeOrderedPayloadA] using
                          option_bind_single_eq
                            (hd (ACEq.argCong (acOp := acOpCM) (l := Label.id "list-cons")
                              [p] (q :: qs) h))
                | cons q qs =>
                    simpa [decodeOrderedPayloadA] using
                      option_bind_single_eq
                        (hd (ACEq.argCong (acOp := acOpCM) (l := Label.id "list-cons")
                          (p :: q :: qs) post h))
          · simpa [decodeOrderedPayloadA, decodeListA, hcons] using
              option_bind_single_eq
                (hd (ACEq.argCong (acOp := acOpCM) (l := Label.id name) pre post h))
      | wild =>
          simpa [decodeOrderedPayloadA, decodeListA] using
            option_bind_single_eq
              (hd (ACEq.argCong (acOp := acOpCM) (l := Label.wild) pre post h))
      | listE c =>
          simpa [decodeOrderedPayloadA, decodeListA] using
            option_bind_single_eq
              (hd (ACEq.argCong (acOp := acOpCM) (l := Label.listE c) pre post h))
      | listCons c =>
          simpa [decodeOrderedPayloadA, decodeListA] using
            option_bind_single_eq
              (hd (ACEq.argCong (acOp := acOpCM) (l := Label.listCons c) pre post h))
      | listOne c =>
          simpa [decodeOrderedPayloadA, decodeListA] using
            option_bind_single_eq
              (hd (ACEq.argCong (acOp := acOpCM) (l := Label.listOne c) pre post h))
  | @substCongB b b' r v h ih =>
      simpa [decodeOrderedPayloadA] using option_bind_single_eq (hd (ACEq.substCongB h))
  | @substCongR b r r' v h ih =>
      simpa [decodeOrderedPayloadA] using option_bind_single_eq (hd (ACEq.substCongR h))

private theorem mapM_decoder_argCong {α : Type*} (d : AST → Option α)
    (hd : ∀ {a b : AST}, ACEq acOpCM a b → d a = d b)
    (pre post : List AST) {a a' : AST} (h : ACEq acOpCM a a') :
    (pre ++ a :: post).mapM d = (pre ++ a' :: post).mapM d := by
  induction pre with
  | nil => simp [hd h]
  | cons _ _ ih => simp [ih]

private theorem decodeOrderedPayloadA_argCong_of_decoder_acEq {α : Type*}
    (d : AST → Option α) (hd : ∀ {a b : AST}, ACEq acOpCM a b → d a = d b)
    (pre post : List AST) {a a' : AST} (h : ACEq acOpCM a a') :
    decodeOrderedPayloadA d (pre ++ a :: post) =
      decodeOrderedPayloadA d (pre ++ a' :: post) := by
  cases pre with
  | nil =>
      cases post with
      | nil => exact decodeOrderedPayloadA_single_acEq_of_decoder_acEq d hd h
      | cons p postTail =>
          simpa [decodeOrderedPayloadA] using mapM_decoder_argCong d hd [] (p :: postTail) h
  | cons p preTail =>
      simpa [decodeOrderedPayloadA] using mapM_decoder_argCong d hd (p :: preTail) post h

private theorem decodePairA_acEq_left {Wave Hash α : Type*}
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ {a b : AST}, ACEq acOpCM a b → dW a = dW b)
    (mk : Wave → Hash → α) {a a' b : AST} (h : ACEq acOpCM a a') :
    decodePairA dW dH mk a b = decodePairA dW dH mk a' b := by
  simp [decodePairA, hW h]

private theorem decodePairA_acEq_right {Wave Hash α : Type*}
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hH : ∀ {a b : AST}, ACEq acOpCM a b → dH a = dH b)
    (mk : Wave → Hash → α) {a b b' : AST} (h : ACEq acOpCM b b') :
    decodePairA dW dH mk a b = decodePairA dW dH mk a b' := by
  simp [decodePairA, hH h]

/-- Fact decoding respects runtime AC-equivalence when both field decoders do. -/
theorem decodeFactA_acEq_of_decoders_acEq {Wave Hash : Type*}
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ {a b : AST}, ACEq acOpCM a b → dW a = dW b)
    (hH : ∀ {a b : AST}, ACEq acOpCM a b → dH a = dH b)
    {a b : AST} (h : ACEq acOpCM a b) :
    decodeFactA dW dH a = decodeFactA dW dH b := by
  induction h with
  | refl _ | substCongB | substCongR => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @comm l a b hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl <;> rfl
  | @assoc l a b c hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl <;> rfl
  | @argCong l pre a a' post h ih =>
      cases l with
      | id name =>
          by_cases hordered : name = "ordered-prefix"
          · subst name
            simp [decodeFactA, decodeOrderedPayloadA_argCong_of_decoder_acEq dH hH pre post h]
          · cases pre with
            | nil =>
                cases post with
                | nil => simp [decodeFactA, hordered]
                | cons _ postTail =>
                    cases postTail with
                    | nil =>
                        by_cases hp : name = "propose"
                        · subst name
                          simp [decodeFactA, decodePairA_acEq_left dW dH hW TrecFact.propose h]
                        · by_cases hq : name = "q-approve"
                          · subst name
                            simp [decodeFactA, decodePairA_acEq_left dW dH hW TrecFact.qApprove h]
                          · by_cases hc : name = "cert-threshold"
                            · subst name
                              simp [decodeFactA, decodePairA_acEq_left dW dH hW TrecFact.certThresh h]
                            · by_cases hf : name = "final"
                              · subst name
                                simp [decodeFactA, decodePairA_acEq_left dW dH hW TrecFact.final h]
                              · by_cases hfl : name = "final-leader"
                                · subst name
                                  simp [decodeFactA,
                                    decodePairA_acEq_left dW dH hW TrecFact.finalLeader h]
                                · simp [decodeFactA, hordered, hp, hq, hc, hf, hfl]
                    | cons _ _ => simp [decodeFactA, hordered]
            | cons _ preTail =>
                cases preTail with
                | nil =>
                    cases post with
                    | nil =>
                        by_cases hp : name = "propose"
                        · subst name
                          simp [decodeFactA, decodePairA_acEq_right dW dH hH TrecFact.propose h]
                        · by_cases hq : name = "q-approve"
                          · subst name
                            simp [decodeFactA, decodePairA_acEq_right dW dH hH TrecFact.qApprove h]
                          · by_cases hc : name = "cert-threshold"
                            · subst name
                              simp [decodeFactA, decodePairA_acEq_right dW dH hH TrecFact.certThresh h]
                            · by_cases hf : name = "final"
                              · subst name
                                simp [decodeFactA, decodePairA_acEq_right dW dH hH TrecFact.final h]
                              · by_cases hfl : name = "final-leader"
                                · subst name
                                  simp [decodeFactA,
                                    decodePairA_acEq_right dW dH hH TrecFact.finalLeader h]
                                · simp [decodeFactA, hordered, hp, hq, hc, hf, hfl]
                    | cons _ _ => simp [decodeFactA, hordered]
                | cons _ _ => simp [decodeFactA, hordered]
      | wild => cases pre <;> simp [decodeFactA]
      | listE _ => cases pre <;> simp [decodeFactA]
      | listCons _ => cases pre <;> simp [decodeFactA]
      | listOne _ => cases pre <;> simp [decodeFactA]

private theorem decodeStateA_stateA_union {Wave Hash : Type*} [DecidableEq Wave]
    [DecidableEq Hash] (dW : AST → Option Wave) (dH : AST → Option Hash) (a b : AST) :
    decodeStateA dW dH (stateA a b) = decodeStateA dW dH a ∪ decodeStateA dW dH b := by
  unfold decodeStateA
  rw [show collectA stateOp (stateA a b) = collectA stateOp a ++ collectA stateOp b from rfl]
  rw [List.filterMap_append]
  ext fact
  simp

private theorem decodeStateA_leaf_of_decodeFact_eq {Wave Hash : Type*} [DecidableEq Wave]
    [DecidableEq Hash] (dW : AST → Option Wave) (dH : AST → Option Hash) {a b : AST}
    (ha : collectA stateOp a = [a]) (hb : collectA stateOp b = [b])
    (hdecode : decodeFactA dW dH a = decodeFactA dW dH b) :
    decodeStateA dW dH a = decodeStateA dW dH b := by
  unfold decodeStateA
  rw [ha, hb]
  cases hda : decodeFactA dW dH a <;> cases hdb : decodeFactA dW dH b <;>
    simp [hda, hdb] at hdecode ⊢
  exact hdecode

private theorem collectA_stateOp_nonstate {l : Label} {args : List AST} (h : l ≠ stateOp) :
    collectA stateOp (.sexp l args) = [.sexp l args] := by
  cases args with
  | nil => rfl
  | cons _ rest =>
      cases rest with
      | nil => rfl
      | cons _ restTail =>
          cases restTail with
          | nil =>
              simp [collectA]
              intro hl
              exact (h (by simpa [stateOp] using hl)).elim
          | cons _ _ => rfl

/-- State decoding respects runtime AC-equivalence when both field decoders do. -/
theorem decodeStateA_acEq_of_decoders_acEq {Wave Hash : Type*} [DecidableEq Wave]
    [DecidableEq Hash] (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ {a b : AST}, ACEq acOpCM a b → dW a = dW b)
    (hH : ∀ {a b : AST}, ACEq acOpCM a b → dH a = dH b)
    {a b : AST} (h : ACEq acOpCM a b) :
    decodeStateA dW dH a = decodeStateA dW dH b := by
  induction h with
  | refl _ | substCongB | substCongR => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @comm l a b hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl
      · exact decodeStateA_cons_comm dW dH a b
      · rfl
  | @assoc l a b c hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl
      · exact decodeStateA_cons_assoc dW dH a b c
      · rfl
  | @argCong l pre a a' post h ih =>
      cases l with
      | id name =>
          by_cases hstate : name = "state"
          · subst name
            cases pre with
            | nil =>
                cases post with
                | nil =>
                    exact decodeStateA_leaf_of_decodeFact_eq dW dH (by rfl) (by rfl)
                      (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
                        (ACEq.argCong (l := stateOp) [] [] h))
                | cons p postTail =>
                    cases postTail with
                    | nil =>
                        change decodeStateA dW dH (stateA a p) =
                          decodeStateA dW dH (stateA a' p)
                        rw [decodeStateA_stateA_union dW dH a p,
                          decodeStateA_stateA_union dW dH a' p, ih]
                    | cons q qs =>
                        exact decodeStateA_leaf_of_decodeFact_eq dW dH (by rfl) (by rfl)
                          (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := stateOp) [] (p :: q :: qs) h))
            | cons p preTail =>
                cases preTail with
                | nil =>
                    cases post with
                    | nil =>
                        change decodeStateA dW dH (stateA p a) =
                          decodeStateA dW dH (stateA p a')
                        rw [decodeStateA_stateA_union dW dH p a,
                          decodeStateA_stateA_union dW dH p a', ih]
                    | cons q qs =>
                        exact decodeStateA_leaf_of_decodeFact_eq dW dH (by rfl) (by rfl)
                          (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := stateOp) [p] (q :: qs) h))
                | cons q qs =>
                    cases qs with
                    | nil =>
                        exact decodeStateA_leaf_of_decodeFact_eq dW dH (by rfl) (by rfl)
                          (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := stateOp) [p, q] post h))
                    | cons r rs =>
                        exact decodeStateA_leaf_of_decodeFact_eq dW dH (by rfl) (by rfl)
                          (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := stateOp) (p :: q :: r :: rs) post h))
          · have hlabel : Label.id name ≠ stateOp := by
              intro hbad
              exact hstate (by simpa [stateOp] using hbad)
            exact decodeStateA_leaf_of_decodeFact_eq dW dH
              (collectA_stateOp_nonstate (l := Label.id name) (args := pre ++ a :: post) hlabel)
              (collectA_stateOp_nonstate (l := Label.id name) (args := pre ++ a' :: post) hlabel)
              (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
                (ACEq.argCong (l := Label.id name) pre post h))
      | wild =>
          exact decodeStateA_leaf_of_decodeFact_eq dW dH
            (collectA_stateOp_nonstate (l := Label.wild) (args := pre ++ a :: post) (by simp [stateOp]))
            (collectA_stateOp_nonstate (l := Label.wild) (args := pre ++ a' :: post)
              (by simp [stateOp]))
            (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.wild) pre post h))
      | listE c =>
          exact decodeStateA_leaf_of_decodeFact_eq dW dH
            (collectA_stateOp_nonstate (l := Label.listE c) (args := pre ++ a :: post)
              (by simp [stateOp]))
            (collectA_stateOp_nonstate (l := Label.listE c) (args := pre ++ a' :: post)
              (by simp [stateOp]))
            (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.listE c) pre post h))
      | listCons c =>
          exact decodeStateA_leaf_of_decodeFact_eq dW dH
            (collectA_stateOp_nonstate (l := Label.listCons c) (args := pre ++ a :: post)
              (by simp [stateOp]))
            (collectA_stateOp_nonstate (l := Label.listCons c) (args := pre ++ a' :: post)
              (by simp [stateOp]))
            (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.listCons c) pre post h))
      | listOne c =>
          exact decodeStateA_leaf_of_decodeFact_eq dW dH
            (collectA_stateOp_nonstate (l := Label.listOne c) (args := pre ++ a :: post)
              (by simp [stateOp]))
            (collectA_stateOp_nonstate (l := Label.listOne c) (args := pre ++ a' :: post)
              (by simp [stateOp]))
            (decodeFactA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.listOne c) pre post h))

/-- Configuration decoding respects runtime AC-equivalence when both field decoders do. -/
theorem astToState_acEq_of_decoders_acEq {Wave Hash : Type*} [DecidableEq Wave]
    [DecidableEq Hash] (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ {a b : AST}, ACEq acOpCM a b → dW a = dW b)
    (hH : ∀ {a b : AST}, ACEq acOpCM a b → dH a = dH b)
    {a b : AST} (h : ACEq acOpCM a b) :
    astToState dW dH a = astToState dW dH b := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @comm l a b hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl
      · simpa [astToState, cmOp, stateOp] using decodeStateA_cons_comm dW dH a b
      · rfl
  | @assoc l a b c hac =>
      rcases acOpCM_eq_state_or_inbox hac with rfl | rfl
      · simpa [astToState, cmOp, stateOp] using decodeStateA_cons_assoc dW dH a b c
      · rfl
  | @argCong l pre a a' post h ih =>
      cases l with
      | id name =>
          by_cases hcm : name = "cm"
          · subst name
            cases pre with
            | nil =>
                cases post with
                | nil =>
                    simpa [astToState, cmOp] using
                      decodeStateA_acEq_of_decoders_acEq dW dH hW hH
                        (ACEq.argCong (l := cmOp) [] [] h)
                | cons p postTail =>
                    cases postTail with
                    | nil =>
                        rfl
                    | cons q qs =>
                        simpa [astToState, cmOp] using
                          decodeStateA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := cmOp) [] (p :: q :: qs) h)
            | cons p preTail =>
                cases preTail with
                | nil =>
                    cases post with
                    | nil =>
                        change decodeStateA dW dH a = decodeStateA dW dH a'
                        exact decodeStateA_acEq_of_decoders_acEq dW dH hW hH h
                    | cons q qs =>
                        simpa [astToState, cmOp] using
                          decodeStateA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := cmOp) [p] (q :: qs) h)
                | cons q qs =>
                    cases qs with
                    | nil =>
                        simpa [astToState, cmOp] using
                          decodeStateA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := cmOp) [p, q] post h)
                    | cons r rs =>
                        simpa [astToState, cmOp] using
                          decodeStateA_acEq_of_decoders_acEq dW dH hW hH
                            (ACEq.argCong (l := cmOp) (p :: q :: r :: rs) post h)
          · simpa [astToState, cmOp, hcm] using
              decodeStateA_acEq_of_decoders_acEq dW dH hW hH
                (ACEq.argCong (l := Label.id name) pre post h)
      | wild =>
          simpa [astToState, cmOp] using
            decodeStateA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.wild) pre post h)
      | listE c =>
          simpa [astToState, cmOp] using
            decodeStateA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.listE c) pre post h)
      | listCons c =>
          simpa [astToState, cmOp] using
            decodeStateA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.listCons c) pre post h)
      | listOne c =>
          simpa [astToState, cmOp] using
            decodeStateA_acEq_of_decoders_acEq dW dH hW hH
              (ACEq.argCong (l := Label.listOne c) pre post h)
  | substCongB h ih =>
      simpa [astToState] using decodeStateA_acEq_of_decoders_acEq dW dH hW hH (ACEq.substCongB h)
  | substCongR h ih =>
      simpa [astToState] using decodeStateA_acEq_of_decoders_acEq dW dH hW hH (ACEq.substCongR h)

/-- A modulo-AC runtime step is backward-sound for any field decoders that respect runtime AC. -/
theorem runtime_step_backward_of_decoders_acEq {Wave Hash : Type*} [DecidableEq Wave]
    [DecidableEq Hash] (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ {a b : AST}, ACEq acOpCM a b → dW a = dW b)
    (hH : ∀ {a b : AST}, ACEq acOpCM a b → dH a = dH b)
    {source target : AST} (hshape : RuntimeConfigShape source)
    (hstep : RewStepModAC acOpCM cmPresentation source target) :
    TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
      astToState dW dH source = astToState dW dH target :=
  runtime_step_backward_of_astToState_acEq dW dH
    (astToState_acEq_of_decoders_acEq dW dH hW hH) hshape hstep

/-- AC can move the second element of an encoded binary collection to the head. -/
theorem collection_second_to_head (op : Label) (hac : acOpCM op = true) (first second rest : AST) :
    ACEq acOpCM (consA op first (consA op second rest))
      (consA op second (consA op first rest)) := by
  have h1 : ACEq acOpCM (consA op first (consA op second rest))
      (consA op (consA op first second) rest) :=
    (ACEq.assoc (acOp := acOpCM) (l := op) (a := first) (b := second) (c := rest) hac).symm
  have h2 : ACEq acOpCM (consA op (consA op first second) rest)
      (consA op (consA op second first) rest) :=
    ACEq.sexp2_fst acOpCM
      (ACEq.comm (acOp := acOpCM) (l := op) (a := first) (b := second) hac)
  have h3 : ACEq acOpCM (consA op (consA op second first) rest)
      (consA op second (consA op first rest)) :=
    ACEq.assoc (acOp := acOpCM) (l := op) (a := second) (b := first) (c := rest) hac
  exact (h1.trans h2).trans h3

/-- AC can move the second inbox event to the head while preserving the rest of the configuration. -/
theorem inbox_second_to_head (first second rest st : AST) :
    ACEq acOpCM
      (cmA (inboxA first (inboxA second rest)) st)
      (cmA (inboxA second (inboxA first rest)) st) := by
  exact ACEq.sexp2_fst acOpCM (collection_second_to_head inboxOp acOpCM_inbox first second rest)

/-- If a tail fact has been moved to the state head, it can pass the cons head modulo AC. -/
theorem state_cons_tail_fact_to_head {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    (head fact : TrecFact Wave Hash) {tail : List (TrecFact Wave Hash)} {rest : AST}
    (hrest : ACEq acOpCM (encStateList eW eH tail) (stateA (encodeFactA eW eH fact) rest)) :
    ACEq acOpCM
      (stateA (encodeFactA eW eH head) (encStateList eW eH tail))
      (stateA (encodeFactA eW eH fact) (stateA (encodeFactA eW eH head) rest)) := by
  have htailHead : ACEq acOpCM
      (stateA (encodeFactA eW eH head) (encStateList eW eH tail))
      (stateA (encodeFactA eW eH head) (stateA (encodeFactA eW eH fact) rest)) :=
    ACEq.sexp2_snd acOpCM hrest
  have hswap : ACEq acOpCM
      (stateA (encodeFactA eW eH head) (stateA (encodeFactA eW eH fact) rest))
      (stateA (encodeFactA eW eH fact) (stateA (encodeFactA eW eH head) rest)) :=
    collection_second_to_head stateOp acOpCM_state
      (encodeFactA eW eH head) (encodeFactA eW eH fact) rest
  exact htailHead.trans hswap

/-- Any fact in an encoded state list can be moved to the AC head. -/
theorem encStateList_mem_head {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    {facts : List (TrecFact Wave Hash)} {fact : TrecFact Wave Hash} (hmem : fact ∈ facts) :
    ∃ rest, ACEq acOpCM (encStateList eW eH facts) (stateA (encodeFactA eW eH fact) rest) := by
  induction facts with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact ⟨encStateList eW eH tail, ACEq.refl _⟩
      · obtain ⟨rest, hrest⟩ := ih htail
        refine ⟨stateA (encodeFactA eW eH head) rest, ?_⟩
        simpa [encStateList] using state_cons_tail_fact_to_head eW eH head fact hrest

/-- A presentation `state` node whose head is an encoded fact decodes as finite-set insertion. -/
theorem decodeStateA_stateA_encodeFactA {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (fact : TrecFact Wave Hash) (rest : AST) :
    decodeStateA dW dH (stateA (encodeFactA eW eH fact) rest) =
      insert fact (decodeStateA dW dH rest) :=
  decodeStateA_cons_encodeFactA eW eH dW dH hW hH fact rest

/-- Moving a state-list fact to the AC head preserves the decoded finite state. -/
theorem encStateList_mem_head_decodes {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {facts : List (TrecFact Wave Hash)} {fact : TrecFact Wave Hash} (hmem : fact ∈ facts) :
    ∃ rest,
      ACEq acOpCM (encStateList eW eH facts) (stateA (encodeFactA eW eH fact) rest) ∧
      decodeStateA dW dH (stateA (encodeFactA eW eH fact) rest) = facts.toFinset := by
  induction facts with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst fact
        refine ⟨encStateList eW eH tail, ACEq.refl _, ?_⟩
        rw [decodeStateA_stateA_encodeFactA eW eH dW dH hW hH head]
        rw [decodeStateA_encStateList eW eH dW dH hW hH tail]
        simp [List.toFinset_cons]
      · obtain ⟨rest, hac, hdecode⟩ := ih htail
        refine ⟨stateA (encodeFactA eW eH head) rest, ?_, ?_⟩
        · simpa [encStateList] using state_cons_tail_fact_to_head eW eH head fact hac
        · have hdecode' : insert fact (decodeStateA dW dH rest) = tail.toFinset :=
            (decodeStateA_stateA_encodeFactA eW eH dW dH hW hH fact rest).symm.trans hdecode
          rw [decodeStateA_stateA_encodeFactA eW eH dW dH hW hH fact]
          rw [decodeStateA_stateA_encodeFactA eW eH dW dH hW hH head]
          calc
            insert fact (insert head (decodeStateA dW dH rest)) =
                insert head (insert fact (decodeStateA dW dH rest)) := by
              ext x
              simp [or_left_comm]
            _ = insert head tail.toFinset := by rw [hdecode']
            _ = (head :: tail).toFinset := by simp [List.toFinset_cons]

/-- Any event in an encoded inbox can be moved to the AC head. -/
theorem encInbox_mem_head {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    {events : List (Event Wave Hash)} {event : Event Wave Hash} (hmem : event ∈ events) :
    ∃ rest, ACEq acOpCM (encInbox eW eH events) (inboxA (encodeEventA eW eH event) rest) := by
  induction events with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact ⟨encInbox eW eH tail, ACEq.refl _⟩
      · obtain ⟨rest, hrest⟩ := ih htail
        refine ⟨inboxA (encodeEventA eW eH head) rest, ?_⟩
        have htailHead : ACEq acOpCM
            (inboxA (encodeEventA eW eH head) (encInbox eW eH tail))
            (inboxA (encodeEventA eW eH head) (inboxA (encodeEventA eW eH event) rest)) :=
          ACEq.sexp2_snd acOpCM hrest
        have hswap : ACEq acOpCM
            (inboxA (encodeEventA eW eH head) (inboxA (encodeEventA eW eH event) rest))
            (inboxA (encodeEventA eW eH event) (inboxA (encodeEventA eW eH head) rest)) :=
          collection_second_to_head inboxOp acOpCM_inbox
            (encodeEventA eW eH head) (encodeEventA eW eH event) rest
        simpa [encInbox] using htailHead.trans hswap

/-- A modulo-AC step may start from any AC-equivalent left representative. -/
theorem rewStepModAC_ac_left {p : Presentation} {source head target : AST}
    (hsource : ACEq acOpCM source head) (hstep : RewStepModAC acOpCM p head target) :
    RewStepModAC acOpCM p source target := by
  rcases hstep with ⟨u, u', hhead, hrel, htarget⟩
  exact ⟨u, u', hsource.trans hhead, hrel, htarget⟩

/-- Encoding the source fact of a derived rule gives the source AST used by the presentation. -/
theorem DerivedKind.encodeSrc {Wave Hash : Type*} (k : DerivedKind)
    (eW : Wave → AST) (eH : Hash → AST) (w : Wave) (h : Hash) :
    encodeFactA eW eH (DerivedKind.srcFact k w h) = DerivedKind.srcA k (eW w) (eH h) := by
  cases k <;> rfl

/-- Encoding the destination fact of a derived rule gives the destination AST used by the presentation. -/
theorem DerivedKind.encodeDst {Wave Hash : Type*} (k : DerivedKind)
    (eW : Wave → AST) (eH : Hash → AST) (w : Wave) (h : Hash) :
    encodeFactA eW eH (DerivedKind.dstFact k w h) = DerivedKind.dstA k (eW w) (eH h) := by
  cases k <;> rfl

/-- Any derived-rule head redex is a runtime step modulo AC. -/
theorem derivedKind_head_modAC (k : DerivedKind) (w h ib rest : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA ib (stateA (DerivedKind.srcA k w h) rest))
      (cmA ib (stateA (DerivedKind.dstA k w h) (stateA (DerivedKind.srcA k w h) rest))) := by
  cases k
  · simpa [DerivedKind.srcA, DerivedKind.dstA] using qapprove_head_modAC w h ib rest
  · simpa [DerivedKind.srcA, DerivedKind.dstA] using certify_head_modAC w h ib rest
  · simpa [DerivedKind.srcA, DerivedKind.dstA] using finalize_head_modAC w h ib rest
  · simpa [DerivedKind.srcA, DerivedKind.dstA] using finalLead_head_modAC w h ib rest

/-- The state fact inserted by an input event. -/
def eventStateFactA {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST) : Event Wave Hash → AST
  | .propose w h => proposeA (eW w) (eH h)
  | .order hs => orderedPrefixPayloadA (encodeListA eH hs)

/-- The coarse fact inserted by an input event. -/
def eventFact {Wave Hash : Type*} : Event Wave Hash → TrecFact Wave Hash
  | .propose w h => TrecFact.propose w h
  | .order hs => TrecFact.orderedPrefix hs

/-- Event state facts are the ordinary AST encodings of their coarse facts. -/
theorem eventStateFactA_eq_encodeFactA {Wave Hash : Type*}
    (eW : Wave → AST) (eH : Hash → AST) (event : Event Wave Hash) :
    eventStateFactA eW eH event = encodeFactA eW eH (eventFact event) := by
  cases event <;> rfl

/-- A decoded input-event target is a real coarse proposal or ordering step. -/
theorem event_step_of_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (s : TrecState Wave Hash) (event : Event Wave Hash) {target : AST}
    (hdecode : astToState dW dH target = insert (eventFact event) s) :
    TrecState.Step s (astToState dW dH target) := by
  rw [hdecode]
  cases event with
  | propose w h => exact TrecState.Step.propose s w h
  | order hs => exact TrecState.Step.order s hs

/-- The target configuration after an input event fires. -/
def eventTargetA {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    (facts : List (TrecFact Wave Hash)) (event : Event Wave Hash) (rest : AST) : AST :=
  cmA rest (stateA (eventStateFactA eW eH event) (encStateList eW eH facts))

/-- An input-event head redex is a runtime step modulo AC. -/
theorem event_head_modAC {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    (event : Event Wave Hash) (rest st : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA (inboxA (encodeEventA eW eH event) rest) st)
      (cmA rest (stateA (eventStateFactA eW eH event) st)) := by
  cases event with
  | propose w h =>
      simpa [encodeEventA, eventStateFactA] using propose_head_modAC (eW w) (eH h) rest st
  | order hs =>
      simpa [encodeEventA, eventStateFactA] using order_head_modAC (encodeListA eH hs) rest st

/-- Any input event in the encoded inbox can fire modulo AC. -/
theorem event_inbox_mem_modAC {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {event : Event Wave Hash}
    (hmem : event ∈ events) :
    ∃ rest, RewStepModAC acOpCM cmPresentation
      (encConfigList eW eH events facts)
      (eventTargetA eW eH facts event rest) := by
  obtain ⟨rest, hinbox⟩ := encInbox_mem_head eW eH hmem
  refine ⟨rest, ?_⟩
  have hcfg : ACEq acOpCM (encConfigList eW eH events facts)
      (cmA (inboxA (encodeEventA eW eH event) rest) (encStateList eW eH facts)) := by
    simpa [encConfigList] using ACEq.sexp2_fst acOpCM hinbox
  exact rewStepModAC_ac_left hcfg
    (by simpa [eventTargetA] using event_head_modAC eW eH event rest (encStateList eW eH facts))

/-- Any input event in the encoded inbox has a runtime step whose target decodes to the inserted fact. -/
theorem event_inbox_mem_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {event : Event Wave Hash}
    (hmem : event ∈ events) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfigList eW eH events facts) target ∧
      astToState dW dH target = insert (eventFact event) facts.toFinset := by
  obtain ⟨rest, hstep⟩ := event_inbox_mem_modAC eW eH (facts := facts) hmem
  refine ⟨eventTargetA eW eH facts event rest, hstep, ?_⟩
  have hdecode :
      decodeStateA dW dH
        (stateA (encodeFactA eW eH (eventFact event)) (encStateList eW eH facts)) =
        insert (eventFact event) facts.toFinset := by
    rw [decodeStateA_stateA_encodeFactA eW eH dW dH hW hH (eventFact event)]
    rw [decodeStateA_encStateList eW eH dW dH hW hH facts]
  simpa [eventTargetA, eventStateFactA_eq_encodeFactA eW eH event, astToState, cmA, cmOp] using hdecode

/-- Any input event in the encoded inbox decodes to a genuine coarse protocol step. -/
theorem event_inbox_mem_forward_step {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {event : Event Wave Hash}
    (hmem : event ∈ events) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfigList eW eH events facts) target ∧
      TrecState.Step facts.toFinset (astToState dW dH target) := by
  obtain ⟨target, hrel, hdecode⟩ :=
    event_inbox_mem_forward_decode eW eH dW dH hW hH hmem
  exact ⟨target, hrel, event_step_of_decode dW dH facts.toFinset event hdecode⟩

/-- If a runtime witness decodes to insertion of an already-present fact, it is a decoded stutter. -/
theorem runtime_step_stutter_of_inserted_fact_mem {Wave Hash : Type*}
    [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    {source target : AST} {facts : List (TrecFact Wave Hash)} {fact : TrecFact Wave Hash}
    (hrel : RewStepModAC acOpCM cmPresentation source target)
    (hdecode : astToState dW dH target = insert fact facts.toFinset) (hfact : fact ∈ facts) :
    ∃ target, RewStepModAC acOpCM cmPresentation source target ∧
      astToState dW dH target = facts.toFinset := by
  refine ⟨target, hrel, ?_⟩
  have hfactSet : fact ∈ facts.toFinset := by
    simpa using hfact
  rw [hdecode]
  exact Finset.insert_eq_of_mem hfactSet

/-- If an input event adds a fact already decoded in the state, the runtime step is a decoded stutter. -/
theorem event_inbox_mem_forward_stutter {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {event : Event Wave Hash}
    (hmem : event ∈ events) (hfact : eventFact event ∈ facts) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfigList eW eH events facts) target ∧
      astToState dW dH target = facts.toFinset := by
  obtain ⟨target, hrel, hdecode⟩ :=
    event_inbox_mem_forward_decode eW eH dW dH hW hH hmem
  exact runtime_step_stutter_of_inserted_fact_mem dW dH hrel hdecode hfact

/-- A proposal event anywhere in the encoded inbox can fire modulo AC. -/
theorem propose_inbox_mem_modAC {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {w : Wave} {h : Hash}
    (hmem : Event.propose w h ∈ events) :
    ∃ rest, RewStepModAC acOpCM cmPresentation
      (encConfigList eW eH events facts)
      (cmA rest (stateA (proposeA (eW w) (eH h)) (encStateList eW eH facts))) := by
  simpa [eventTargetA, eventStateFactA] using event_inbox_mem_modAC eW eH (facts := facts) hmem

/-- An order event anywhere in the encoded inbox can fire modulo AC. -/
theorem order_inbox_mem_modAC {Wave Hash : Type*} (eW : Wave → AST) (eH : Hash → AST)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {hs : List Hash}
    (hmem : Event.order hs ∈ events) :
    ∃ rest, RewStepModAC acOpCM cmPresentation
      (encConfigList eW eH events facts)
      (cmA rest (stateA (orderedPrefixPayloadA (encodeListA eH hs)) (encStateList eW eH facts))) := by
  simpa [eventTargetA, eventStateFactA] using event_inbox_mem_modAC eW eH (facts := facts) hmem

/-- A headed derived-rule source fact gives the matching runtime step. -/
theorem derived_state_head_modAC {Wave Hash : Type*} (k : DerivedKind)
    (eW : Wave → AST) (eH : Hash → AST)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {w : Wave} {h : Hash}
    {rest : AST}
    (hstate : ACEq acOpCM (encStateList eW eH facts)
      (stateA (DerivedKind.srcA k (eW w) (eH h)) rest)) :
    RewStepModAC acOpCM cmPresentation
      (encConfigList eW eH events facts)
      (cmA (encInbox eW eH events)
        (stateA (DerivedKind.dstA k (eW w) (eH h))
          (stateA (DerivedKind.srcA k (eW w) (eH h)) rest))) := by
  have hcfg : ACEq acOpCM (encConfigList eW eH events facts)
      (cmA (encInbox eW eH events) (stateA (DerivedKind.srcA k (eW w) (eH h)) rest)) := by
    simpa [encConfigList] using ACEq.sexp2_snd acOpCM hstate
  exact rewStepModAC_ac_left hcfg
    (derivedKind_head_modAC k (eW w) (eH h) (encInbox eW eH events) rest)

/-- A derived fact anywhere in the encoded state can fire its derived rule modulo AC. -/
theorem derived_state_mem_modAC {Wave Hash : Type*} (k : DerivedKind)
    (eW : Wave → AST) (eH : Hash → AST)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {w : Wave} {h : Hash}
    (hmem : DerivedKind.srcFact k w h ∈ facts) :
    ∃ rest, RewStepModAC acOpCM cmPresentation
      (encConfigList eW eH events facts)
      (cmA (encInbox eW eH events)
        (stateA (DerivedKind.dstA k (eW w) (eH h))
          (stateA (DerivedKind.srcA k (eW w) (eH h)) rest))) := by
  obtain ⟨rest, hstate⟩ := encStateList_mem_head eW eH hmem
  refine ⟨rest, ?_⟩
  have hstate' : ACEq acOpCM (encStateList eW eH facts)
      (stateA (DerivedKind.srcA k (eW w) (eH h)) rest) := by
    simpa [DerivedKind.encodeSrc] using hstate
  exact derived_state_head_modAC k eW eH hstate'

/-- A derived fact anywhere in the encoded state has a runtime step whose target decodes to the inserted
    derived fact. -/
theorem derived_state_mem_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {w : Wave} {h : Hash}
    (hmem : DerivedKind.srcFact k w h ∈ facts) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfigList eW eH events facts) target ∧
      astToState dW dH target = insert (DerivedKind.dstFact k w h) facts.toFinset := by
  obtain ⟨rest, hhead, hdecodeHead⟩ := encStateList_mem_head_decodes eW eH dW dH hW hH hmem
  refine ⟨cmA (encInbox eW eH events)
    (stateA (DerivedKind.dstA k (eW w) (eH h))
      (stateA (DerivedKind.srcA k (eW w) (eH h)) rest)), ?_, ?_⟩
  · have hstate' : ACEq acOpCM (encStateList eW eH facts)
        (stateA (DerivedKind.srcA k (eW w) (eH h)) rest) := by
      simpa [DerivedKind.encodeSrc] using hhead
    exact derived_state_head_modAC k eW eH hstate'
  · have hdecode :
        decodeStateA dW dH
          (stateA (encodeFactA eW eH (DerivedKind.dstFact k w h))
          (stateA (encodeFactA eW eH (DerivedKind.srcFact k w h)) rest)) =
          insert (DerivedKind.dstFact k w h) facts.toFinset := by
      rw [decodeStateA_stateA_encodeFactA eW eH dW dH hW hH (DerivedKind.dstFact k w h)]
      simpa using congrArg (fun s => insert (DerivedKind.dstFact k w h) s) hdecodeHead
    simpa [astToState, cmA, cmOp, DerivedKind.encodeSrc, DerivedKind.encodeDst] using hdecode

/-- Any derived-rule precondition in the encoded state decodes to a genuine coarse protocol step. -/
theorem derived_state_mem_forward_step {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {w : Wave} {h : Hash}
    (hmem : DerivedKind.srcFact k w h ∈ facts) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfigList eW eH events facts) target ∧
      TrecState.Step facts.toFinset (astToState dW dH target) := by
  obtain ⟨target, hrel, hdecode⟩ :=
    derived_state_mem_forward_decode k eW eH dW dH hW hH hmem
  have hpre : DerivedKind.srcFact k w h ∈ facts.toFinset := by
    simpa using hmem
  exact ⟨target, hrel, derived_step_of_decode k dW dH hpre hdecode⟩

/-- If a derived rule adds a fact already decoded in the state, the runtime step is a decoded stutter. -/
theorem derived_state_mem_forward_stutter {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {events : List (Event Wave Hash)} {facts : List (TrecFact Wave Hash)} {w : Wave} {h : Hash}
    (hsrc : DerivedKind.srcFact k w h ∈ facts) (hdst : DerivedKind.dstFact k w h ∈ facts) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfigList eW eH events facts) target ∧
      astToState dW dH target = facts.toFinset := by
  obtain ⟨target, hrel, hdecode⟩ :=
    derived_state_mem_forward_decode k eW eH dW dH hW hH hsrc
  exact runtime_step_stutter_of_inserted_fact_mem dW dH hrel hdecode hdst

/-- A single input event supplied in the inbox has a runtime step whose target decodes to the inserted
    coarse fact. -/
theorem event_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (s : TrecState Wave Hash) (event : Event Wave Hash) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH [event] s) target ∧
      astToState dW dH target = insert (eventFact event) s := by
  obtain ⟨target, hrel, hdecode⟩ :=
    event_inbox_mem_forward_decode eW eH dW dH hW hH
      (events := [event]) (facts := s.toList) (event := event) (by simp)
  refine ⟨target, ?_, ?_⟩
  · simpa [encConfig, encState, encConfigList] using hrel
  · simpa [Finset.toList_toFinset] using hdecode

/-- A single input event supplied in the inbox has a runtime step that decodes to a coarse protocol step. -/
theorem event_forward_step {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (s : TrecState Wave Hash) (event : Event Wave Hash) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH [event] s) target ∧
      TrecState.Step s (astToState dW dH target) := by
  obtain ⟨target, hrel, hdecode⟩ := event_forward_decode eW eH dW dH hW hH s event
  exact ⟨target, hrel, event_step_of_decode dW dH s event hdecode⟩

/-- A single input event that adds an already-present fact is a decoded stutter. -/
theorem event_forward_stutter {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s : TrecState Wave Hash} {event : Event Wave Hash} (hfact : eventFact event ∈ s) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH [event] s) target ∧
      astToState dW dH target = s := by
  have hfactList : eventFact event ∈ s.toList := Finset.mem_toList.mpr hfact
  obtain ⟨target, hrel, hdecode⟩ :=
    event_inbox_mem_forward_stutter eW eH dW dH hW hH
      (events := [event]) (facts := s.toList) (event := event) (by simp) hfactList
  refine ⟨target, ?_, ?_⟩
  · simpa [encConfig, encState, encConfigList] using hrel
  · simpa [Finset.toList_toFinset] using hdecode

/-- A derived-rule precondition in a finite state has a runtime step whose target decodes to the
    corresponding inserted fact. -/
theorem derived_step_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s : TrecState Wave Hash} {w : Wave} {h : Hash} (hpre : DerivedKind.srcFact k w h ∈ s) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH [] s) target ∧
      astToState dW dH target = insert (DerivedKind.dstFact k w h) s := by
  have hmem : DerivedKind.srcFact k w h ∈ s.toList := Finset.mem_toList.mpr hpre
  obtain ⟨target, hrel, hdecode⟩ :=
    derived_state_mem_forward_decode k eW eH dW dH hW hH
      (events := ([] : List (Event Wave Hash))) (facts := s.toList) hmem
  refine ⟨target, ?_, ?_⟩
  · simpa [encConfig, encState, encConfigList] using hrel
  · simpa [Finset.toList_toFinset] using hdecode

/-- A derived-rule precondition in a finite state has a runtime step that decodes to a coarse protocol
    step. -/
theorem derived_step_forward_step {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s : TrecState Wave Hash} {w : Wave} {h : Hash} (hpre : DerivedKind.srcFact k w h ∈ s) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH [] s) target ∧
      TrecState.Step s (astToState dW dH target) := by
  obtain ⟨target, hrel, hdecode⟩ :=
    derived_step_forward_decode k eW eH dW dH hW hH hpre
  exact ⟨target, hrel, derived_step_of_decode k dW dH hpre hdecode⟩

/-- A derived rule that adds an already-present fact is a decoded stutter. -/
theorem derived_step_forward_stutter {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s : TrecState Wave Hash} {w : Wave} {h : Hash}
    (hsrc : DerivedKind.srcFact k w h ∈ s) (hdst : DerivedKind.dstFact k w h ∈ s) :
    ∃ target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH [] s) target ∧
      astToState dW dH target = s := by
  have hsrcList : DerivedKind.srcFact k w h ∈ s.toList := Finset.mem_toList.mpr hsrc
  have hdstList : DerivedKind.dstFact k w h ∈ s.toList := Finset.mem_toList.mpr hdst
  obtain ⟨target, hrel, hdecode⟩ :=
    derived_state_mem_forward_stutter k eW eH dW dH hW hH
      (events := ([] : List (Event Wave Hash))) (facts := s.toList) hsrcList hdstList
  refine ⟨target, ?_, ?_⟩
  · simpa [encConfig, encState, encConfigList] using hrel
  · simpa [Finset.toList_toFinset] using hdecode

/-- A runtime step witness whose target decodes to a chosen coarse state. -/
def RuntimeStepDecodesTo {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (events : List (Event Wave Hash)) (s targetState : TrecState Wave Hash) : Prop :=
  ∃ target,
    RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
    astToState dW dH target = targetState

/-- A runtime step witness whose decoded target is a coarse protocol successor. -/
def RuntimeStepIsCoarseStep {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (events : List (Event Wave Hash)) (s : TrecState Wave Hash) : Prop :=
  ∃ target,
    RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
    TrecState.Step s (astToState dW dH target)

/-- Every coarse protocol step has a runtime witness that decodes to its target. -/
def RuntimeForwardComplete {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash) :
    Prop :=
  ∀ {s s' : TrecState Wave Hash},
    TrecState.Step s s' → ∃ events, RuntimeStepDecodesTo eW eH dW dH events s s'

/-- One supplied input event runs to a decoded coarse protocol successor. -/
def RuntimeEventSound {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash) :
    Prop :=
  ∀ (s : TrecState Wave Hash) (event : Event Wave Hash),
    RuntimeStepIsCoarseStep eW eH dW dH [event] s

/-- One derived-rule precondition fact runs to a decoded coarse protocol successor. -/
def RuntimeDerivedSound {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash) :
    Prop :=
  ∀ (k : DerivedKind) {s : TrecState Wave Hash} {w : Wave} {h : Hash},
    DerivedKind.srcFact k w h ∈ s → RuntimeStepIsCoarseStep eW eH dW dH [] s

/-- A duplicate input event runs to a decoded stutter. -/
def RuntimeEventStutterSound {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash) :
    Prop :=
  ∀ {s : TrecState Wave Hash} {event : Event Wave Hash},
    eventFact event ∈ s → RuntimeStepDecodesTo eW eH dW dH [event] s s

/-- A derived rule whose output fact is already present runs to a decoded stutter. -/
def RuntimeDerivedStutterSound {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash) :
    Prop :=
  ∀ (k : DerivedKind) {s : TrecState Wave Hash} {w : Wave} {h : Hash},
    DerivedKind.srcFact k w h ∈ s →
      DerivedKind.dstFact k w h ∈ s → RuntimeStepDecodesTo eW eH dW dH [] s s

/-- The scoped runtime bridge surface currently proved for the Cordial Miners presentation. -/
def RuntimeScopedBridge {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash) :
    Prop :=
  RuntimeForwardComplete eW eH dW dH ∧
    RuntimeEventSound eW eH dW dH ∧
    RuntimeDerivedSound eW eH dW dH ∧
    RuntimeEventStutterSound eW eH dW dH ∧
    RuntimeDerivedStutterSound eW eH dW dH

/-- Package an input-event runtime step in the existential shape used by the coarse forward theorem. -/
private theorem trec_event_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (s : TrecState Wave Hash) (event : Event Wave Hash) :
    ∃ events target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
      astToState dW dH target = insert (eventFact event) s := by
  obtain ⟨target, hrel, hdecode⟩ := event_forward_decode eW eH dW dH hW hH s event
  exact ⟨[event], target, hrel, hdecode⟩

/-- Package a derived-rule runtime step in the existential shape used by the coarse forward theorem. -/
private theorem trec_derived_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (k : DerivedKind) (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s : TrecState Wave Hash} {w : Wave} {h : Hash} (hpre : DerivedKind.srcFact k w h ∈ s) :
    ∃ events target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
      astToState dW dH target = insert (DerivedKind.dstFact k w h) s := by
  obtain ⟨target, hrel, hdecode⟩ := derived_step_forward_decode k eW eH dW dH hW hH hpre
  exact ⟨[], target, hrel, hdecode⟩

/-- Every coarse `TrecState.Step` has a matching runtime step whose target decodes to the coarse target.
    The theorem is stated through `astToState` because runtime collections are multisets while `TrecState`
    is a `Finset`. Re-adding an existing fact duplicates an AST leaf but decodes to the same finite set. -/
theorem trec_step_forward_decode {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s s' : TrecState Wave Hash} (hstep : TrecState.Step s s') :
    ∃ events target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
      astToState dW dH target = s' := by
  cases hstep with
  | propose w h =>
      simpa [eventFact] using
        trec_event_forward_decode eW eH dW dH hW hH s (Event.propose w h)
  | qapprove w h hpre =>
      simpa [DerivedKind.srcFact, DerivedKind.dstFact] using
        trec_derived_forward_decode DerivedKind.qapprove eW eH dW dH hW hH hpre
  | certify w h hpre =>
      simpa [DerivedKind.srcFact, DerivedKind.dstFact] using
        trec_derived_forward_decode DerivedKind.certify eW eH dW dH hW hH hpre
  | finalize w h hpre =>
      simpa [DerivedKind.srcFact, DerivedKind.dstFact] using
        trec_derived_forward_decode DerivedKind.finalize eW eH dW dH hW hH hpre
  | finalLead w h hpre =>
      simpa [DerivedKind.srcFact, DerivedKind.dstFact] using
        trec_derived_forward_decode DerivedKind.finalLead eW eH dW dH hW hH hpre
  | order hs =>
      simpa [eventFact] using
        trec_event_forward_decode eW eH dW dH hW hH s (Event.order hs)

/-- If the coarse source is reachable, the decoded target produced by the runtime forward witness is
    reachable too. The proved forward bridge gives this reachability transfer. -/
theorem trec_step_forward_reachable {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s s' : TrecState Wave Hash}
    (hreach : Relation.ReflTransGen TrecState.Step (∅ : TrecState Wave Hash) s)
    (hstep : TrecState.Step s s') :
    ∃ events target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
      astToState dW dH target = s' ∧
      Relation.ReflTransGen TrecState.Step (∅ : TrecState Wave Hash) (astToState dW dH target) := by
  obtain ⟨events, target, hrel, hdecode⟩ :=
    trec_step_forward_decode eW eH dW dH hW hH hstep
  refine ⟨events, target, hrel, hdecode, ?_⟩
  rw [hdecode]
  exact Relation.ReflTransGen.tail hreach hstep

/-- Coarse well-formedness transfers to the decoded target of the runtime witness produced by the
    forward bridge, provided the source state was coarse-reachable. -/
theorem trec_step_forward_wf {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    {s s' : TrecState Wave Hash}
    (hreach : Relation.ReflTransGen TrecState.Step (∅ : TrecState Wave Hash) s)
    (hstep : TrecState.Step s s') :
    ∃ events target,
      RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
      astToState dW dH target = s' ∧
      TrecWF (astToState dW dH target) := by
  obtain ⟨events, target, hrel, hdecode, hreachTarget⟩ :=
    trec_step_forward_reachable eW eH dW dH hW hH hreach hstep
  exact ⟨events, target, hrel, hdecode, trec_reachable_wf hreachTarget⟩

/-- The proved scoped bridge for the declared Cordial Miners runtime fragments.

The first component is forward completeness for every coarse `TrecState.Step`. The next two components
are decoded soundness facts for the input-event and derived-rule fragments. The last two components are
decoded stutter facts for duplicate input events and duplicate derived facts. The theorem is not the full
arbitrary-`RewStepModAC` backward theorem. -/
theorem scoped_runtime_bridge {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h) :
    RuntimeScopedBridge eW eH dW dH := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s s' hstep
    exact trec_step_forward_decode eW eH dW dH hW hH hstep
  · intro s event
    exact event_forward_step eW eH dW dH hW hH s event
  · intro k s w h hpre
    exact derived_step_forward_step k eW eH dW dH hW hH hpre
  · intro s event hfact
    exact event_forward_stutter eW eH dW dH hW hH hfact
  · intro k s w h hsrc hdst
    exact derived_step_forward_stutter k eW eH dW dH hW hH hsrc hdst

/-- A proposal event in the second inbox position can fire modulo AC, leaving the first event pending. -/
theorem propose_second_inbox_modAC (first w h ibrest st : AST) :
    RewStepModAC acOpCM cmPresentation
      (cmA (inboxA first (inboxA (evProposeA w h) ibrest)) st)
      (cmA (inboxA first ibrest) (stateA (proposeA w h) st)) := by
  refine ⟨cmA (inboxA (evProposeA w h) (inboxA first ibrest)) st,
    cmA (inboxA first ibrest) (stateA (proposeA w h) st), ?_, ?_, ACEq.refl _⟩
  · exact inbox_second_to_head first (evProposeA w h) ibrest st
  · exact RewStep.top
      (reduces_of_applyBaseRewrite cmPresentation proposeRule _ _
        (by simp [cmPresentation, Presentation.rewrites]) (by rfl))

end CordialMiners.Runtime
