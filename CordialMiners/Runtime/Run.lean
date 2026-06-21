/-
Module: CordialMiners.Runtime.Run
Layer: Runtime
Purpose: Executable Cordial Miners runs on the verified MeTTaIL runtime presentation. The examples use
  `evalAC'` over `cmPresentation`, not the older bespoke simulator, and check the resulting AST and
  decoded coarse state at build time.
Imports: CordialMiners.Runtime.Simulation, MeTTaILProofs.DecEq
Trusted boundary: none
Main exports: buriedProposalStart, orderStart, finalityStart, finalityExpectedState,
  dNat_acEq, decodeFactA_dNat_acEq, decodeStateA_dNat_acEq, astToState_dNat_acEq,
  runtime_step_backward_nat,
  buriedProposal_eval_modAC, order_eval_modAC, finality_eval_run_modAC,
  finality_runtime_state_decodes, finality_trec_reachable, finality_runtime_trec_reachable,
  finality_runtime_wf, finality_runtime_final_needs_propose
Open obligations: these are executable regression checks plus concrete transfer corollaries for the
  worked run. The generic relation bridge lives in `CordialMiners.Runtime.Simulation`.
-/
import CordialMiners.Runtime.Simulation
import MeTTaILProofs.DecEq

namespace CordialMiners.Runtime

open MeTTaIL
open MeTTaIL.AC

attribute [local simp] cmA inboxA stateA evProposeA evOrderPayloadA orderedPrefixPayloadA
  proposeA qApproveA certThreshA finalA finalLeaderA appA stateOp inboxOp cmOp consA cmNil symA

/-- The executable Nat decoder ignores every runtime AC rearrangement. -/
theorem dNat_acEq {a b : AST} (h : ACEq acOpCM a b) : dNat a = dNat b := by
  induction h with
  | refl _ | substCongB | substCongR => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comm => simp [dNat]
  | assoc => simp [dNat]
  | argCong => simp [dNat]

/-- Runtime AC rearrangement does not change executable Nat-list decoding. -/
theorem decodeListA_dNat_acEq {a b : AST} (h : ACEq acOpCM a b) :
    decodeListA dNat a = decodeListA dNat b :=
  decodeListA_acEq_of_decoder_acEq dNat (fun h => dNat_acEq h) h

/-- Executable Nat fact decoding ignores every runtime AC rearrangement. -/
theorem decodeFactA_dNat_acEq {a b : AST} (h : ACEq acOpCM a b) :
    decodeFactA dNat dNat a = decodeFactA dNat dNat b :=
  decodeFactA_acEq_of_decoders_acEq dNat dNat
    (fun h => dNat_acEq h) (fun h => dNat_acEq h) h

/-- Executable Nat state decoding ignores every runtime AC rearrangement. -/
theorem decodeStateA_dNat_acEq {a b : AST} (h : ACEq acOpCM a b) :
    decodeStateA dNat dNat a = decodeStateA dNat dNat b :=
  decodeStateA_acEq_of_decoders_acEq dNat dNat
    (fun h => dNat_acEq h) (fun h => dNat_acEq h) h

/-- Executable Nat configuration decoding factors through runtime AC equivalence. -/
theorem astToState_dNat_acEq {a b : AST} (h : ACEq acOpCM a b) :
    astToState dNat dNat a = astToState dNat dNat b :=
  astToState_acEq_of_decoders_acEq dNat dNat
    (fun h => dNat_acEq h) (fun h => dNat_acEq h) h

/-- The executable Nat/Nat runtime never takes a modulo-AC step outside the coarse protocol, up to
    decoded stutter. -/
theorem runtime_step_backward_nat {source target : AST}
    (hshape : RuntimeConfigShape source)
    (hstep : RewStepModAC acOpCM cmPresentation source target) :
    TrecState.Step (astToState dNat dNat source) (astToState dNat dNat target) ∨
      astToState dNat dNat source = astToState dNat dNat target :=
  runtime_step_backward_of_decoders_acEq dNat dNat
    (fun h => dNat_acEq h) (fun h => dNat_acEq h) hshape hstep

/-- Compose five adjacent steps into one reflexive-transitive run. -/
private theorem reflTransGen_five {α : Type*} {r : α → α → Prop} {a b c d e f : α}
    (h1 : r a b) (h2 : r b c) (h3 : r c d) (h4 : r d e) (h5 : r e f) :
    Relation.ReflTransGen r a f :=
  ((((Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2)).trans
    (Relation.ReflTransGen.single h3)).trans (Relation.ReflTransGen.single h4)).trans
      (Relation.ReflTransGen.single h5)

/-- A proposal event buried after an order event. One runtime step must find it modulo AC. -/
def buriedProposalStart : AST :=
  encConfigList eNat eNat [Event.order [2, 3], Event.propose 1 10] []

/-- The expected result after consuming the buried proposal event. -/
def afterBuriedProposal : AST :=
  encConfigList eNat eNat [Event.order [2, 3]] [TrecFact.propose 1 10]

#eval oneStepAC' acOpCM cmPresentation buriedProposalStart == some afterBuriedProposal

/-- AC matching finds and consumes a non-head proposal event. -/
example : oneStepAC' acOpCM cmPresentation buriedProposalStart = some afterBuriedProposal := by
  rfl

/-- The fuel-bounded runner agrees with the one-step result. -/
example : evalAC' acOpCM cmPresentation 1 buriedProposalStart = afterBuriedProposal := by
  rfl

/-- The buried proposal run is also a genuine runtime step modulo AC. -/
theorem buriedProposal_modAC :
    RewStepModAC acOpCM cmPresentation buriedProposalStart afterBuriedProposal := by
  simpa [buriedProposalStart, afterBuriedProposal, encConfigList, encInbox, encStateList, encodeEventA,
    encodeFactA, consA, cmNil, symA] using
      propose_second_inbox_modAC (encodeEventA eNat eNat (Event.order [2, 3])) (eNat 1) (eNat 10)
        cmNil cmNil

/-- The executable buried-proposal step has a runtime relation witness. -/
theorem buriedProposal_eval_modAC :
    RewStepModAC acOpCM cmPresentation buriedProposalStart
      (evalAC' acOpCM cmPresentation 1 buriedProposalStart) := by
  rw [show evalAC' acOpCM cmPresentation 1 buriedProposalStart = afterBuriedProposal from rfl]
  exact buriedProposal_modAC

/-- A multi-hash order event. The payload uses the runtime AST list codec. -/
def orderStart : AST :=
  encConfigList eNat eNat [Event.order [1, 2, 3]] []

/-- The expected result after consuming the order event. -/
def afterOrder : AST :=
  encConfigList eNat eNat [] [TrecFact.orderedPrefix [1, 2, 3]]

#eval evalAC' acOpCM cmPresentation 1 orderStart == afterOrder

/-- The runtime consumes a variable-length order event and adds the ordered-prefix fact. -/
example : evalAC' acOpCM cmPresentation 1 orderStart = afterOrder := by
  rfl

/-- Decode the state facts from a Nat/Nat runtime configuration. -/
def runtimeFactList : AST → List (TrecFact Nat Nat)
  | .sexp (.id "cm") [_, st] => (collectA stateOp st).filterMap (decodeFactA dNat dNat)
  | st => (collectA stateOp st).filterMap (decodeFactA dNat dNat)

/-- Decoding an executable Nat/Nat state list returns the fact list used to build it. -/
theorem runtimeFactList_encStateList :
    ∀ facts : List (TrecFact Nat Nat),
      (collectA stateOp (encStateList eNat eNat facts)).filterMap (decodeFactA dNat dNat) = facts := by
  exact decodedFacts_encStateList eNat eNat dNat dNat dNat_eNat dNat_eNat

/-- Decoding an executable Nat/Nat configuration returns its encoded fact list. -/
theorem runtimeFactList_encConfigList (events : List (Event Nat Nat))
    (facts : List (TrecFact Nat Nat)) :
    runtimeFactList (encConfigList eNat eNat events facts) = facts := by
  simp only [runtimeFactList, encConfigList, cmOp]
  exact runtimeFactList_encStateList facts

/-- Decoding the runtime result recovers the coarse ordered-prefix fact. -/
example : runtimeFactList afterOrder = [TrecFact.orderedPrefix [1, 2, 3]] := by
  simp [afterOrder, runtimeFactList_encConfigList]

/-- The order run is also a genuine runtime step modulo AC. -/
theorem order_modAC : RewStepModAC acOpCM cmPresentation orderStart afterOrder := by
  simpa [orderStart, afterOrder, encConfigList, encInbox, encStateList, encodeEventA, encodeFactA,
    consA, cmNil, symA] using
      order_head_modAC (encodeListA eNat [1, 2, 3]) cmNil cmNil

/-- The executable order step has a runtime relation witness. -/
theorem order_eval_modAC :
    RewStepModAC acOpCM cmPresentation orderStart
      (evalAC' acOpCM cmPresentation 1 orderStart) := by
  rw [show evalAC' acOpCM cmPresentation 1 orderStart = afterOrder from rfl]
  exact order_modAC

/-- A one-block finality scenario driven entirely by runtime rewrite rules. -/
def finalityStart : AST :=
  encConfigList eNat eNat [Event.propose 1 10] []

/-- The finality scenario after the proposal input has been consumed. -/
def finalityAfterPropose : AST :=
  encConfigList eNat eNat [] [TrecFact.propose 1 10]

/-- The finality scenario after quorum approval. -/
def finalityAfterQApprove : AST :=
  encConfigList eNat eNat [] [TrecFact.qApprove 1 10, TrecFact.propose 1 10]

/-- The finality scenario after threshold certification. -/
def finalityAfterCert : AST :=
  encConfigList eNat eNat [] [
    TrecFact.certThresh 1 10,
    TrecFact.qApprove 1 10,
    TrecFact.propose 1 10
  ]

/-- The finality scenario after finality. -/
def finalityAfterFinal : AST :=
  encConfigList eNat eNat [] [
    TrecFact.final 1 10,
    TrecFact.certThresh 1 10,
    TrecFact.qApprove 1 10,
    TrecFact.propose 1 10
  ]

/-- The expected AST after proposal, approval, certificate, finality, and final-leader derivation. -/
def finalityExpectedConfig : AST :=
  encConfigList eNat eNat [] [
    TrecFact.finalLeader 1 10,
    TrecFact.final 1 10,
    TrecFact.certThresh 1 10,
    TrecFact.qApprove 1 10,
    TrecFact.propose 1 10
  ]

/-- The decoded coarse facts expected from the finality run. -/
def finalityExpectedFacts : List (TrecFact Nat Nat) := [
  TrecFact.finalLeader 1 10,
  TrecFact.final 1 10,
  TrecFact.certThresh 1 10,
  TrecFact.qApprove 1 10,
  TrecFact.propose 1 10
]

/-- The decoded coarse state expected from the finality run. -/
def finalityExpectedState : TrecState Nat Nat := finalityExpectedFacts.toFinset

/-- The same finality facts as a set literal, useful when reading this file as a protocol example. -/
example : finalityExpectedState = ({
  TrecFact.propose 1 10,
  TrecFact.qApprove 1 10,
  TrecFact.certThresh 1 10,
  TrecFact.final 1 10,
  TrecFact.finalLeader 1 10
} : TrecState Nat Nat) := by
  decide

#eval evalAC' acOpCM cmPresentation 5 finalityStart == finalityExpectedConfig

/-- Five runtime steps drive proposal through final-leader derivation. -/
example : evalAC' acOpCM cmPresentation 5 finalityStart = finalityExpectedConfig := by
  rfl

/-- The finality run decodes to the expected coarse protocol facts. -/
example :
    runtimeFactList (evalAC' acOpCM cmPresentation 5 finalityStart) = finalityExpectedFacts := by
  rw [show evalAC' acOpCM cmPresentation 5 finalityStart = finalityExpectedConfig from rfl]
  simp [finalityExpectedConfig, finalityExpectedFacts, runtimeFactList_encConfigList]

/-- The five-step finality run is reachable in the runtime relation modulo AC. -/
theorem finality_run_modAC :
    Relation.ReflTransGen (RewStepModAC acOpCM cmPresentation) finalityStart finalityExpectedConfig := by
  have h1 : RewStepModAC acOpCM cmPresentation finalityStart finalityAfterPropose := by
    simpa [finalityStart, finalityAfterPropose, encConfigList, encInbox, encStateList, encodeEventA,
      encodeFactA, consA, cmNil, symA] using
        propose_head_modAC (eNat 1) (eNat 10) cmNil cmNil
  have h2 : RewStepModAC acOpCM cmPresentation finalityAfterPropose finalityAfterQApprove := by
    simpa [finalityAfterPropose, finalityAfterQApprove, encConfigList, encInbox, encStateList,
      encodeFactA, consA, cmNil, symA] using
        qapprove_head_modAC (eNat 1) (eNat 10) cmNil cmNil
  have h3 : RewStepModAC acOpCM cmPresentation finalityAfterQApprove finalityAfterCert := by
    simpa [finalityAfterQApprove, finalityAfterCert, encConfigList, encInbox, encStateList,
      encodeFactA, consA, cmNil, symA] using
        certify_head_modAC (eNat 1) (eNat 10) cmNil
          (stateA (proposeA (eNat 1) (eNat 10)) cmNil)
  have h4 : RewStepModAC acOpCM cmPresentation finalityAfterCert finalityAfterFinal := by
    simpa [finalityAfterCert, finalityAfterFinal, encConfigList, encInbox, encStateList,
      encodeFactA, consA, cmNil, symA] using
        finalize_head_modAC (eNat 1) (eNat 10) cmNil
          (stateA (qApproveA (eNat 1) (eNat 10)) (stateA (proposeA (eNat 1) (eNat 10)) cmNil))
  have h5 : RewStepModAC acOpCM cmPresentation finalityAfterFinal finalityExpectedConfig := by
    simpa [finalityAfterFinal, finalityExpectedConfig, encConfigList, encInbox, encStateList,
      encodeFactA, consA, cmNil, symA] using
        finalLead_head_modAC (eNat 1) (eNat 10) cmNil
          (stateA (certThreshA (eNat 1) (eNat 10))
            (stateA (qApproveA (eNat 1) (eNat 10)) (stateA (proposeA (eNat 1) (eNat 10)) cmNil)))
  exact reflTransGen_five h1 h2 h3 h4 h5

/-- The executable finality run has a runtime relation witness. -/
theorem finality_eval_run_modAC :
    Relation.ReflTransGen (RewStepModAC acOpCM cmPresentation) finalityStart
      (evalAC' acOpCM cmPresentation 5 finalityStart) := by
  rw [show evalAC' acOpCM cmPresentation 5 finalityStart = finalityExpectedConfig from rfl]
  exact finality_run_modAC

/-- The executable finality run decodes to the expected coarse state. -/
theorem finality_runtime_state_decodes :
    astToState dNat dNat (evalAC' acOpCM cmPresentation 5 finalityStart) = finalityExpectedState := by
  rw [show evalAC' acOpCM cmPresentation 5 finalityStart = finalityExpectedConfig from rfl]
  simpa [finalityExpectedConfig, finalityExpectedState, finalityExpectedFacts] using
    astToState_encConfigList eNat eNat dNat dNat ⟨dNat_eNat, dNat_eNat⟩
      ([] : List (Event Nat Nat)) finalityExpectedFacts

/-- The decoded coarse state of the finality run is reachable in `T_rec`. -/
theorem finality_trec_reachable :
    Relation.ReflTransGen TrecState.Step (∅ : TrecState Nat Nat) finalityExpectedState := by
  let p : TrecFact Nat Nat := TrecFact.propose 1 10
  let q : TrecFact Nat Nat := TrecFact.qApprove 1 10
  let c : TrecFact Nat Nat := TrecFact.certThresh 1 10
  let f : TrecFact Nat Nat := TrecFact.final 1 10
  let l : TrecFact Nat Nat := TrecFact.finalLeader 1 10
  have h1 : TrecState.Step (∅ : TrecState Nat Nat) (insert p ∅) :=
    TrecState.Step.propose ∅ 1 10
  have h2 : TrecState.Step (insert p ∅) (insert q (insert p ∅)) :=
    TrecState.Step.qapprove (insert p ∅) 1 10 (by simp [p])
  have h3 : TrecState.Step (insert q (insert p ∅)) (insert c (insert q (insert p ∅))) :=
    TrecState.Step.certify (insert q (insert p ∅)) 1 10 (by simp [q])
  have h4 : TrecState.Step
      (insert c (insert q (insert p ∅)))
      (insert f (insert c (insert q (insert p ∅)))) :=
    TrecState.Step.finalize (insert c (insert q (insert p ∅))) 1 10 (by simp [c])
  have h5 : TrecState.Step
      (insert f (insert c (insert q (insert p ∅))))
      (insert l (insert f (insert c (insert q (insert p ∅))))) :=
    TrecState.Step.finalLead (insert f (insert c (insert q (insert p ∅)))) 1 10 (by simp [f])
  have hreach :
      Relation.ReflTransGen TrecState.Step (∅ : TrecState Nat Nat)
        (insert l (insert f (insert c (insert q (insert p ∅))))) :=
    reflTransGen_five h1 h2 h3 h4 h5
  simpa [finalityExpectedState, finalityExpectedFacts, p, q, c, f, l] using hreach

/-- The decoded result of the executable finality run is coarse-reachable. -/
theorem finality_runtime_trec_reachable :
    Relation.ReflTransGen TrecState.Step (∅ : TrecState Nat Nat)
      (astToState dNat dNat (evalAC' acOpCM cmPresentation 5 finalityStart)) := by
  rw [finality_runtime_state_decodes]
  exact finality_trec_reachable

/-- The decoded result of the executable finality run satisfies the coarse well-formedness invariant. -/
theorem finality_runtime_wf :
    TrecWF (astToState dNat dNat (evalAC' acOpCM cmPresentation 5 finalityStart)) :=
  trec_reachable_wf finality_runtime_trec_reachable

/-- The final fact in the executable runtime result is backed by the matching proposal fact. -/
theorem finality_runtime_final_needs_propose :
    TrecFact.propose 1 10 ∈ astToState dNat dNat (evalAC' acOpCM cmPresentation 5 finalityStart) := by
  have hfinal :
      TrecFact.final 1 10 ∈
        astToState dNat dNat (evalAC' acOpCM cmPresentation 5 finalityStart) := by
    rw [finality_runtime_state_decodes]
    simp [finalityExpectedState, finalityExpectedFacts]
  exact trec_final_needs_propose finality_runtime_trec_reachable hfinal

end CordialMiners.Runtime
