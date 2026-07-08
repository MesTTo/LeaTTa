-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Runtime.Encode
Layer: Runtime
Purpose: Encode the coarse Cordial Miners state into the real MeTTaIL AST used by the verified runtime.
  Facts use the same heads as the existing shallow CMIR extraction, but target `MeTTaIL.AST` directly.
  States and inboxes are binary collections under labels that the runtime can later treat as AC.
Imports: CordialMiners.Extract.MettaIL, MeTTaIL.Syntax
Trusted boundary: none
Main exports: Event, eNat, dNat, sexprToAST, encodeListA, decodeListA, encodeFactA, decodeFactA,
  encState, encInbox, encConfig, astToInbox, astToState, decodeFactA_encodeFactA,
  decodeEventA_encodeEventA, decodeInboxA_encInbox, decodeInboxA_cons_encodeEventA,
  decodeStateA_cons_comm, decodeStateA_cons_assoc, astToState_inbox_irrelevant,
  astToState_cons_comm, astToState_cons_assoc,
  decodeStateA_cons_encodeFactA_stutter, astToState_cons_encodeFactA_stutter,
  NoEmbeddedConfig, RuntimeConfigShape, noEmbeddedConfig_encodeFactA,
  noEmbeddedConfig_encodeEventA, runtimeConfigShape_encConfigList, runtimeConfigShape_encConfig,
  astToInbox_encConfigList, astToInbox_encConfig, astToState_encConfig
Open obligations: `astToState` drops malformed leaves and collapses duplicates through `Finset`; the
  simulation layer states the exact abstraction theorem that uses this decoder.
-/
import CordialMiners.Extract.MettaIL
import MeTTaIL.Syntax
import Std.Data.String.ToNat

namespace CordialMiners.Runtime

open MeTTaIL

variable {Wave Hash : Type*}

/-- A runtime input event. Proposal and ordering are spontaneous in `TrecState.Step`, so the runtime
    carries them in an inbox and consumes them by rewriting. -/
inductive Event (Wave Hash : Type*) where
  | propose (w : Wave) (h : Hash)
  | order (hs : List Hash)
deriving DecidableEq, Repr

/-- A nullary symbol leaf in the MeTTaIL AST. -/
def symA (s : String) : AST := .sexp (.id s) []

/-- An S-expression with a string head. -/
def appA (s : String) (args : List AST) : AST := .sexp (.id s) args

/-- Runtime list terminator for variable-length payloads. -/
def listNilA : AST := appA "list-nil" []

/-- Runtime list cons for variable-length payloads. -/
def listConsA (head tail : AST) : AST := appA "list-cons" [head, tail]

/-- Encode a Lean list as an explicit AST list payload. -/
def encodeListA {α : Type*} (e : α → AST) : List α → AST
  | [] => listNilA
  | x :: xs => listConsA (e x) (encodeListA e xs)

/-- Decode an explicit AST list payload. -/
def decodeListA {α : Type*} (d : AST → Option α) : AST → Option (List α)
  | .sexp (.id "list-nil") [] => some []
  | .sexp (.id "list-cons") [head, tail] =>
      match d head, decodeListA d tail with
      | some x, some xs => some (x :: xs)
      | _, _ => none
  | _ => none

/-- Encoded AST lists decode back to the original Lean list under a left-inverse element codec. -/
theorem decodeListA_encodeListA {α : Type*} (e : α → AST) (d : AST → Option α)
    (hd : ∀ a, d (e a) = some a) : ∀ xs : List α, decodeListA d (encodeListA e xs) = some xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeListA, decodeListA, listConsA, appA, hd, ih]

/-- Executable natural-number encoder used by the Nat/Nat demo instance. -/
def eNat (n : Nat) : AST := symA (Nat.repr n)

/-- Executable natural-number decoder used by the Nat/Nat demo instance. -/
def dNat : AST → Option Nat
  | .sexp (.id s) [] => s.toNat?
  | _ => none

/-- The Nat codec is lossless on encoded naturals. -/
theorem dNat_eNat (n : Nat) : dNat (eNat n) = some n := by
  simp [dNat, eNat, symA, Nat.toNat?_repr]

/-- Convert the older shallow CMIR atom syntax into the real MeTTaIL AST. Applications whose first
    element is a symbol become a headed AST node; other lists are preserved under an `app` head. -/
def sexprToAST : Sexpr → AST
  | .sym s => symA s
  | .num n => eNat n
  | .app (.sym h :: args) => appA h (args.map sexprToAST)
  | .app args => appA "app" (args.map sexprToAST)

/-- Encode one coarse protocol fact into the runtime AST. -/
def encodeFactA (eW : Wave → AST) (eH : Hash → AST) : TrecFact Wave Hash → AST
  | .propose w h => appA "propose" [eW w, eH h]
  | .qApprove w h => appA "q-approve" [eW w, eH h]
  | .certThresh w h => appA "cert-threshold" [eW w, eH h]
  | .final w h => appA "final" [eW w, eH h]
  | .finalLeader w h => appA "final-leader" [eW w, eH h]
  | .orderedPrefix hs => appA "ordered-prefix" [encodeListA eH hs]

/-- Decode a pair of Wave/Hash fields and assemble the result. -/
def decodePairA {α : Type*} (dW : AST → Option Wave) (dH : AST → Option Hash)
    (mk : Wave → Hash → α) (a b : AST) : Option α :=
  match dW a, dH b with
  | some w, some h => some (mk w h)
  | _, _ => none

/-- Decode an ordered-prefix payload. Runtime terms use one explicit list payload. Legacy shallow
    extraction used variadic hash arguments, so this decoder accepts that shape too. -/
def decodeOrderedPayloadA (dH : AST → Option Hash) : List AST → Option (List Hash)
  | [.sexp (.id "list-nil") []] => some []
  | [.sexp (.id "list-cons") [head, tail]] => decodeListA dH (listConsA head tail)
  | rest => rest.mapM dH

/-- Runtime ordered payloads decode back to the original hash list. -/
theorem decodeOrderedPayloadA_encodeListA (eH : Hash → AST) (dH : AST → Option Hash)
    (hH : ∀ h, dH (eH h) = some h) :
    ∀ hs : List Hash, decodeOrderedPayloadA dH [encodeListA eH hs] = some hs := by
  intro hs
  cases hs with
  | nil => rfl
  | cons h hs =>
      simpa [decodeOrderedPayloadA, encodeListA, listConsA, appA] using
        decodeListA_encodeListA eH dH hH (h :: hs)

/-- Decode one runtime AST fact back to the coarse protocol fact language. Unknown heads or malformed
    arities decode to `none`. -/
def decodeFactA (dW : AST → Option Wave) (dH : AST → Option Hash) :
    AST → Option (TrecFact Wave Hash)
  | .sexp (.id "propose") [a, b] => decodePairA dW dH TrecFact.propose a b
  | .sexp (.id "q-approve") [a, b] => decodePairA dW dH TrecFact.qApprove a b
  | .sexp (.id "cert-threshold") [a, b] => decodePairA dW dH TrecFact.certThresh a b
  | .sexp (.id "final") [a, b] => decodePairA dW dH TrecFact.final a b
  | .sexp (.id "final-leader") [a, b] => decodePairA dW dH TrecFact.finalLeader a b
  | .sexp (.id "ordered-prefix") rest => (decodeOrderedPayloadA dH rest).map TrecFact.orderedPrefix
  | _ => none

/-- A list of encoded AST items decodes back to the original list. -/
theorem mapM_map_leftInvA (e : Hash → AST) (d : AST → Option Hash)
    (hd : ∀ a, d (e a) = some a) : ∀ l : List Hash, (l.map e).mapM d = some l := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, hd, ih]

/-- Direct AST extraction is lossless for individual facts under left-inverse field codecs. -/
theorem decodeFactA_encodeFactA (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h) :
    ∀ f : TrecFact Wave Hash, decodeFactA dW dH (encodeFactA eW eH f) = some f := by
  intro f
  cases f with
  | propose w h => simp [encodeFactA, decodeFactA, decodePairA, appA, hW, hH]
  | qApprove w h => simp [encodeFactA, decodeFactA, decodePairA, appA, hW, hH]
  | certThresh w h => simp [encodeFactA, decodeFactA, decodePairA, appA, hW, hH]
  | final w h => simp [encodeFactA, decodeFactA, decodePairA, appA, hW, hH]
  | finalLeader w h => simp [encodeFactA, decodeFactA, decodePairA, appA, hW, hH]
  | orderedPrefix hs =>
      simp [encodeFactA, decodeFactA, appA, decodeOrderedPayloadA_encodeListA eH dH hH hs]

/-- The AC label used for coarse states. -/
def stateOp : Label := .id "state"

/-- The AC label used for pending input events. -/
def inboxOp : Label := .id "inbox"

/-- The top-level runtime configuration label. -/
def cmOp : Label := .id "cm"

/-- Sentinel leaf for right-nested AC collections. The sentinel is not an identity law. -/
def cmNil : AST := symA "nil"

/-- A binary collection node. -/
def consA (op : Label) (x rest : AST) : AST := .sexp op [x, rest]

/-- Encode one runtime input event. -/
def encodeEventA (eW : Wave → AST) (eH : Hash → AST) : Event Wave Hash → AST
  | .propose w h => appA "ev-propose" [eW w, eH h]
  | .order hs => appA "ev-order" [encodeListA eH hs]

/-- Decode one runtime input event. -/
def decodeEventA (dW : AST → Option Wave) (dH : AST → Option Hash) :
    AST → Option (Event Wave Hash)
  | .sexp (.id "ev-propose") [a, b] => decodePairA dW dH Event.propose a b
  | .sexp (.id "ev-order") rest => (decodeOrderedPayloadA dH rest).map Event.order
  | _ => none

/-- Encoded runtime input events decode back to the original event under left-inverse field codecs. -/
theorem decodeEventA_encodeEventA (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h) :
    ∀ event : Event Wave Hash, decodeEventA dW dH (encodeEventA eW eH event) = some event := by
  intro event
  cases event with
  | propose w h => simp [encodeEventA, decodeEventA, decodePairA, appA, hW, hH]
  | order hs =>
      simp [encodeEventA, decodeEventA, appA, decodeOrderedPayloadA_encodeListA eH dH hH hs]

/-- Encode a list of coarse facts as a right-nested `state` collection. Executable scenarios use this
    encoder. -/
def encStateList (eW : Wave → AST) (eH : Hash → AST) (facts : List (TrecFact Wave Hash)) : AST :=
  (facts.map (encodeFactA eW eH)).foldr (fun f rest => consA stateOp f rest) cmNil

/-- Encode a finite coarse state as a right-nested `state` collection. The wrapper is noncomputable
    because `Finset` forgets order; executable scenarios use `encStateList`. -/
noncomputable def encState [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (s : TrecState Wave Hash) : AST :=
  encStateList eW eH s.toList

/-- Encode an inbox as a right-nested `inbox` collection. -/
def encInbox (eW : Wave → AST) (eH : Hash → AST) (events : List (Event Wave Hash)) : AST :=
  (events.map (encodeEventA eW eH)).foldr (fun ev rest => consA inboxOp ev rest) cmNil

/-- Encode a full runtime configuration from an ordered fact list. Executable scenarios use this encoder. -/
def encConfigList (eW : Wave → AST) (eH : Hash → AST) (events : List (Event Wave Hash))
    (facts : List (TrecFact Wave Hash)) : AST :=
  .sexp cmOp [encInbox eW eH events, encStateList eW eH facts]

/-- Encode a full runtime configuration. -/
noncomputable def encConfig [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (events : List (Event Wave Hash))
    (s : TrecState Wave Hash) : AST :=
  .sexp cmOp [encInbox eW eH events, encState eW eH s]

mutual
  /-- Payloads are clean when they do not contain an embedded runtime configuration head. Payload
      cleanliness is the
      syntactic side condition needed by the later backward classifier: protocol rules should fire at the
      configuration boundary, not inside encoded field payloads. -/
  def NoEmbeddedConfig : AST → Prop
    | .var _ => True
    | .sexp l args => l ≠ cmOp ∧ NoEmbeddedConfigList args
    | .subst body repl _ => NoEmbeddedConfig body ∧ NoEmbeddedConfig repl

  /-- List form of `NoEmbeddedConfig`, used to keep the AST recursion structurally visible to Lean. -/
  def NoEmbeddedConfigList : List AST → Prop
    | [] => True
    | t :: ts => NoEmbeddedConfig t ∧ NoEmbeddedConfigList ts
end

/-- A well-shaped runtime configuration has one top-level `cm` node and clean inbox and state payloads. -/
def RuntimeConfigShape : AST → Prop
  | .sexp l [ib, st] => l = cmOp ∧ NoEmbeddedConfig ib ∧ NoEmbeddedConfig st
  | _ => False

/-- The runtime sentinel is clean payload. -/
theorem noEmbeddedConfig_cmNil : NoEmbeddedConfig cmNil := by
  simp [NoEmbeddedConfig, NoEmbeddedConfigList, cmNil, symA, cmOp]

/-- Explicit AST lists preserve payload cleanliness. -/
theorem noEmbeddedConfig_encodeListA {α : Type*} (e : α → AST)
    (h : ∀ x, NoEmbeddedConfig (e x)) :
    ∀ xs : List α, NoEmbeddedConfig (encodeListA e xs) := by
  intro xs
  induction xs with
  | nil =>
      simp [encodeListA, listNilA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp]
  | cons x xs ih =>
      simp [encodeListA, listConsA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, h x, ih]

/-- Encoded facts are clean when their field codecs are clean. -/
theorem noEmbeddedConfig_encodeFactA (eW : Wave → AST) (eH : Hash → AST)
    (hW : ∀ w, NoEmbeddedConfig (eW w)) (hH : ∀ h, NoEmbeddedConfig (eH h)) :
    ∀ fact : TrecFact Wave Hash, NoEmbeddedConfig (encodeFactA eW eH fact) := by
  intro fact
  cases fact with
  | propose w h => simp [encodeFactA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, hW w, hH h]
  | qApprove w h => simp [encodeFactA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, hW w, hH h]
  | certThresh w h =>
      simp [encodeFactA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, hW w, hH h]
  | final w h => simp [encodeFactA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, hW w, hH h]
  | finalLeader w h =>
      simp [encodeFactA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, hW w, hH h]
  | orderedPrefix hs =>
      simp [encodeFactA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp,
        noEmbeddedConfig_encodeListA eH hH hs]

/-- Encoded input events are clean when their field codecs are clean. -/
theorem noEmbeddedConfig_encodeEventA (eW : Wave → AST) (eH : Hash → AST)
    (hW : ∀ w, NoEmbeddedConfig (eW w)) (hH : ∀ h, NoEmbeddedConfig (eH h)) :
    ∀ event : Event Wave Hash, NoEmbeddedConfig (encodeEventA eW eH event) := by
  intro event
  cases event with
  | propose w h => simp [encodeEventA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp, hW w, hH h]
  | order hs =>
      simp [encodeEventA, appA, NoEmbeddedConfig, NoEmbeddedConfigList, cmOp,
        noEmbeddedConfig_encodeListA eH hH hs]

/-- Encoded state lists are clean when their field codecs are clean. -/
theorem noEmbeddedConfig_encStateList (eW : Wave → AST) (eH : Hash → AST)
    (hW : ∀ w, NoEmbeddedConfig (eW w)) (hH : ∀ h, NoEmbeddedConfig (eH h)) :
    ∀ facts : List (TrecFact Wave Hash), NoEmbeddedConfig (encStateList eW eH facts) := by
  intro facts
  induction facts with
  | nil => exact noEmbeddedConfig_cmNil
  | cons fact facts ih =>
      change NoEmbeddedConfig (consA stateOp (encodeFactA eW eH fact) (encStateList eW eH facts))
      simp [consA, NoEmbeddedConfig, NoEmbeddedConfigList, stateOp, cmOp,
        noEmbeddedConfig_encodeFactA eW eH hW hH fact, ih]

/-- Encoded inboxes are clean when their field codecs are clean. -/
theorem noEmbeddedConfig_encInbox (eW : Wave → AST) (eH : Hash → AST)
    (hW : ∀ w, NoEmbeddedConfig (eW w)) (hH : ∀ h, NoEmbeddedConfig (eH h)) :
    ∀ events : List (Event Wave Hash), NoEmbeddedConfig (encInbox eW eH events) := by
  intro events
  induction events with
  | nil => exact noEmbeddedConfig_cmNil
  | cons event events ih =>
      change NoEmbeddedConfig (consA inboxOp (encodeEventA eW eH event) (encInbox eW eH events))
      simp [consA, NoEmbeddedConfig, NoEmbeddedConfigList, inboxOp, cmOp,
        noEmbeddedConfig_encodeEventA eW eH hW hH event, ih]

/-- Encoded configuration lists satisfy the runtime configuration shape invariant. -/
theorem runtimeConfigShape_encConfigList (eW : Wave → AST) (eH : Hash → AST)
    (hW : ∀ w, NoEmbeddedConfig (eW w)) (hH : ∀ h, NoEmbeddedConfig (eH h))
    (events : List (Event Wave Hash)) (facts : List (TrecFact Wave Hash)) :
    RuntimeConfigShape (encConfigList eW eH events facts) := by
  simp [RuntimeConfigShape, encConfigList,
    noEmbeddedConfig_encInbox eW eH hW hH events,
    noEmbeddedConfig_encStateList eW eH hW hH facts]

/-- Encoded finite-state configurations satisfy the runtime configuration shape invariant. -/
theorem runtimeConfigShape_encConfig [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST)
    (hW : ∀ w, NoEmbeddedConfig (eW w)) (hH : ∀ h, NoEmbeddedConfig (eH h))
    (events : List (Event Wave Hash)) (s : TrecState Wave Hash) :
    RuntimeConfigShape (encConfig eW eH events s) := by
  simpa [encConfig, encState, encConfigList] using
    runtimeConfigShape_encConfigList eW eH hW hH events s.toList

/-- Flatten one binary collection label. Nonmatching nodes are leaves. -/
def collectA (op : Label) : AST → List AST
  | .sexp l [a, b] => if l == op then collectA op a ++ collectA op b else [.sexp l [a, b]]
  | t => [t]

/-- Decoding a right-nested encoded collection recovers the source list when encoded elements are leaves
    for that collection and the element codec is lossless. -/
theorem decodedCollection_foldr {α : Type*} (op : Label) (encode : α → AST) (decode : AST → Option α)
    (hLeaf : ∀ x, collectA op (encode x) = [encode x])
    (hDecode : ∀ x, decode (encode x) = some x) (hNil : decode cmNil = none)
    (hSelf : (op == op) = true) :
    ∀ xs : List α,
      (collectA op ((xs.map encode).foldr (fun x rest => consA op x rest) cmNil)).filterMap decode =
        xs := by
  intro xs
  induction xs with
  | nil =>
      change [cmNil].filterMap decode = []
      simp [hNil]
  | cons x xs ih =>
      have hCollect :
          collectA op (consA op (encode x) ((xs.map encode).foldr (fun y rest => consA op y rest) cmNil)) =
            collectA op (encode x) ++
              collectA op ((xs.map encode).foldr (fun y rest => consA op y rest) cmNil) := by
        simp [consA, collectA, hSelf]
      change
        (collectA op
          (consA op (encode x) ((xs.map encode).foldr (fun y rest => consA op y rest) cmNil))).filterMap
          decode = x :: xs
      rw [hCollect, List.filterMap_append, hLeaf x, ih]
      simp [hDecode x]

/-- Decode an inbox collection to the list of well-formed input events it contains. Malformed leaves are
    ignored, matching the state decoder's abstraction. -/
def decodeInboxA (dW : AST → Option Wave) (dH : AST → Option Hash) (t : AST) :
    List (Event Wave Hash) :=
  (collectA inboxOp t).filterMap (decodeEventA dW dH)

/-- Decode the inbox component of a runtime configuration. A bare inbox collection is accepted too, which
    mirrors `astToState` and keeps intermediate lemmas small. -/
def astToInbox (dW : AST → Option Wave) (dH : AST → Option Hash) : AST → List (Event Wave Hash)
  | .sexp (.id "cm") [ib, _] => decodeInboxA dW dH ib
  | ib => decodeInboxA dW dH ib

/-- Decode a state collection, ignoring malformed leaves and collapsing duplicates. -/
def decodeStateA [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (t : AST) : TrecState Wave Hash :=
  ((collectA stateOp t).filterMap (decodeFactA dW dH)).toFinset

/-- Decode the state component of a runtime configuration. A bare collection is accepted too, which makes
    the abstraction useful in intermediate lemmas. -/
def astToState [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) : AST → TrecState Wave Hash
  | .sexp (.id "cm") [_, st] => decodeStateA dW dH st
  | st => decodeStateA dW dH st

/-- Encoded facts are leaves of the runtime state collection. -/
theorem collectA_stateOp_encodeFactA (eW : Wave → AST) (eH : Hash → AST)
    (fact : TrecFact Wave Hash) :
    collectA stateOp (encodeFactA eW eH fact) = [encodeFactA eW eH fact] := by
  cases fact <;> rfl

/-- Encoded input events are leaves of the runtime inbox collection. -/
theorem collectA_inboxOp_encodeEventA (eW : Wave → AST) (eH : Hash → AST)
    (event : Event Wave Hash) :
    collectA inboxOp (encodeEventA eW eH event) = [encodeEventA eW eH event] := by
  cases event <;> rfl

/-- Decoding the flattened encoded state list recovers the source fact list. -/
theorem decodedFacts_encStateList (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h) :
    ∀ facts : List (TrecFact Wave Hash),
      (collectA stateOp (encStateList eW eH facts)).filterMap (decodeFactA dW dH) = facts := by
  intro facts
  simpa [encStateList] using
    decodedCollection_foldr stateOp (encodeFactA eW eH) (decodeFactA dW dH)
      (collectA_stateOp_encodeFactA eW eH)
      (decodeFactA_encodeFactA eW eH dW dH hW hH) (by rfl) (by rfl) facts

/-- Decoding an encoded state list gives the finite set represented by the list. -/
theorem decodeStateA_encStateList [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (facts : List (TrecFact Wave Hash)) :
    decodeStateA dW dH (encStateList eW eH facts) = facts.toFinset := by
  simp [decodeStateA, decodedFacts_encStateList eW eH dW dH hW hH facts]

/-- Decoding an encoded inbox recovers the source event list. -/
theorem decodeInboxA_encInbox (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h) :
    ∀ events : List (Event Wave Hash), decodeInboxA dW dH (encInbox eW eH events) = events := by
  intro events
  simpa [decodeInboxA, encInbox] using
    decodedCollection_foldr inboxOp (encodeEventA eW eH) (decodeEventA dW dH)
      (collectA_inboxOp_encodeEventA eW eH)
      (decodeEventA_encodeEventA eW eH dW dH hW hH) (by rfl) (by rfl) events

/-- Prepending an encoded event to a decoded inbox collection conses the decoded event. -/
theorem decodeInboxA_cons_encodeEventA (eW : Wave → AST) (eH : Hash → AST)
    (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (event : Event Wave Hash) (rest : AST) :
    decodeInboxA dW dH (consA inboxOp (encodeEventA eW eH event) rest) =
      event :: decodeInboxA dW dH rest := by
  unfold decodeInboxA
  rw [show collectA inboxOp (consA inboxOp (encodeEventA eW eH event) rest) =
      collectA inboxOp (encodeEventA eW eH event) ++ collectA inboxOp rest from rfl]
  rw [List.filterMap_append, collectA_inboxOp_encodeEventA eW eH event]
  simp [decodeEventA_encodeEventA eW eH dW dH hW hH event]

/-- Prepending an encoded fact to a decoded state collection inserts the decoded fact. -/
theorem decodeStateA_cons_encodeFactA [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (fact : TrecFact Wave Hash) (rest : AST) :
    decodeStateA dW dH (consA stateOp (encodeFactA eW eH fact) rest) =
      insert fact (decodeStateA dW dH rest) := by
  unfold decodeStateA
  rw [show collectA stateOp (consA stateOp (encodeFactA eW eH fact) rest) =
      collectA stateOp (encodeFactA eW eH fact) ++ collectA stateOp rest from rfl]
  rw [List.filterMap_append, collectA_stateOp_encodeFactA eW eH fact]
  simp [decodeFactA_encodeFactA eW eH dW dH hW hH fact]

/-- Decoding a `state` collection is insensitive to the AC commutativity generator. -/
theorem decodeStateA_cons_comm [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (a b : AST) :
    decodeStateA dW dH (consA stateOp a b) =
      decodeStateA dW dH (consA stateOp b a) := by
  unfold decodeStateA
  rw [show collectA stateOp (consA stateOp a b) = collectA stateOp a ++ collectA stateOp b from rfl]
  rw [show collectA stateOp (consA stateOp b a) = collectA stateOp b ++ collectA stateOp a from rfl]
  rw [List.filterMap_append, List.filterMap_append]
  ext fact
  simp [or_comm]

/-- Decoding a `state` collection is insensitive to the AC associativity generator. -/
theorem decodeStateA_cons_assoc [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (a b c : AST) :
    decodeStateA dW dH (consA stateOp (consA stateOp a b) c) =
      decodeStateA dW dH (consA stateOp a (consA stateOp b c)) := by
  unfold decodeStateA
  rw [show collectA stateOp (consA stateOp (consA stateOp a b) c) =
      collectA stateOp (consA stateOp a b) ++ collectA stateOp c from rfl]
  rw [show collectA stateOp (consA stateOp a (consA stateOp b c)) =
      collectA stateOp a ++ collectA stateOp (consA stateOp b c) from rfl]
  rw [show collectA stateOp (consA stateOp a b) =
      collectA stateOp a ++ collectA stateOp b from rfl]
  rw [show collectA stateOp (consA stateOp b c) =
      collectA stateOp b ++ collectA stateOp c from rfl]
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append, List.filterMap_append]
  simp [List.append_assoc]

/-- The decoded state of a runtime configuration does not depend on its inbox component. -/
theorem astToState_inbox_irrelevant [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (ib ib' st : AST) :
    astToState dW dH (.sexp cmOp [ib, st]) =
      astToState dW dH (.sexp cmOp [ib', st]) := by
  rfl

/-- The decoded state of a runtime configuration is insensitive to state commutativity. -/
theorem astToState_cons_comm [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (ib a b : AST) :
    astToState dW dH (.sexp cmOp [ib, consA stateOp a b]) =
      astToState dW dH (.sexp cmOp [ib, consA stateOp b a]) := by
  simpa [astToState, cmOp] using decodeStateA_cons_comm dW dH a b

/-- The decoded state of a runtime configuration is insensitive to state associativity. -/
theorem astToState_cons_assoc [DecidableEq Wave] [DecidableEq Hash]
    (dW : AST → Option Wave) (dH : AST → Option Hash) (ib a b c : AST) :
    astToState dW dH (.sexp cmOp [ib, consA stateOp (consA stateOp a b) c]) =
      astToState dW dH (.sexp cmOp [ib, consA stateOp a (consA stateOp b c)]) := by
  simpa [astToState, cmOp] using decodeStateA_cons_assoc dW dH a b c

/-- Re-adding an already decoded fact is a stutter under `decodeStateA`. -/
theorem decodeStateA_cons_encodeFactA_stutter [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (fact : TrecFact Wave Hash) (rest : AST)
    (hmem : fact ∈ decodeStateA dW dH rest) :
    decodeStateA dW dH (consA stateOp (encodeFactA eW eH fact) rest) =
      decodeStateA dW dH rest := by
  rw [decodeStateA_cons_encodeFactA eW eH dW dH hW hH fact rest]
  exact Finset.insert_eq_of_mem hmem

/-- Re-adding an already decoded fact to a runtime configuration is a stutter under `astToState`. -/
theorem astToState_cons_encodeFactA_stutter [DecidableEq Wave] [DecidableEq Hash]
    (eW : Wave → AST) (eH : Hash → AST) (dW : AST → Option Wave) (dH : AST → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h)
    (fact : TrecFact Wave Hash) (ib rest : AST)
    (hmem : fact ∈ astToState dW dH (.sexp cmOp [ib, rest])) :
    astToState dW dH (.sexp cmOp [ib, consA stateOp (encodeFactA eW eH fact) rest]) =
      astToState dW dH (.sexp cmOp [ib, rest]) := by
  have hmem' : fact ∈ decodeStateA dW dH rest := by
    simpa [astToState, cmOp] using hmem
  simp [astToState, cmOp, decodeStateA_cons_encodeFactA_stutter eW eH dW dH hW hH fact rest hmem']

section ConfigRoundTrips

variable (eW : Wave → AST) (eH : Hash → AST)
variable (dW : AST → Option Wave) (dH : AST → Option Hash)

/-- Decoding an encoded configuration list gives back its inbox event list. -/
theorem astToInbox_encConfigList
    (hCodec : (∀ w, dW (eW w) = some w) ∧ (∀ h, dH (eH h) = some h))
    (events : List (Event Wave Hash)) (facts : List (TrecFact Wave Hash)) :
    astToInbox dW dH (encConfigList eW eH events facts) = events := by
  simp [astToInbox, encConfigList, cmOp,
    decodeInboxA_encInbox eW eH dW dH hCodec.1 hCodec.2 events]

/-- Decoding an encoded finite-set configuration gives back its inbox event list. -/
theorem astToInbox_encConfig [DecidableEq Wave] [DecidableEq Hash]
    (hCodec : (∀ w, dW (eW w) = some w) ∧ (∀ h, dH (eH h) = some h))
    (events : List (Event Wave Hash)) (s : TrecState Wave Hash) :
    astToInbox dW dH (encConfig eW eH events s) = events := by
  simp [astToInbox, encConfig, cmOp, decodeInboxA_encInbox eW eH dW dH hCodec.1 hCodec.2 events]

/-- Decoding an encoded configuration list gives the finite set represented by its state list. -/
theorem astToState_encConfigList [DecidableEq Wave] [DecidableEq Hash]
    (hCodec : (∀ w, dW (eW w) = some w) ∧ (∀ h, dH (eH h) = some h))
    (events : List (Event Wave Hash)) (facts : List (TrecFact Wave Hash)) :
    astToState dW dH (encConfigList eW eH events facts) = facts.toFinset := by
  simp [astToState, encConfigList, cmOp,
    decodeStateA_encStateList eW eH dW dH hCodec.1 hCodec.2 facts]

/-- Decoding an encoded finite-set configuration gives back its coarse state. -/
theorem astToState_encConfig [DecidableEq Wave] [DecidableEq Hash]
    (hCodec : (∀ w, dW (eW w) = some w) ∧ (∀ h, dH (eH h) = some h))
    (events : List (Event Wave Hash)) (s : TrecState Wave Hash) :
    astToState dW dH (encConfig eW eH events s) = s := by
  simpa [encConfig, encState, encConfigList, Finset.toList_toFinset] using
    astToState_encConfigList eW eH dW dH hCodec events s.toList

end ConfigRoundTrips

end CordialMiners.Runtime
