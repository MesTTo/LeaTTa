/-
Module: CordialMiners.Runtime.Presentation
Layer: Runtime
Purpose: The Cordial Miners coarse protocol as a MeTTaIL presentation. The rules operate on encoded
  runtime configurations `(cm inbox state)`. Gated rules match an existing fact inside the AC state
  collection and add the derived fact. Input rules consume a matching event from the AC inbox and add
  the proposed or ordered fact.
Imports: CordialMiners.Runtime.Encode, MeTTaILProofs.ACMatch
Trusted boundary: none
Main exports: acOpCM, cmPresentation, proposeRule, qapproveRule, certifyRule, finalizeRule,
  finalLeadRule, orderRule
Open obligations: the simulation layer proves that these six rewrites match `TrecState.Step` up to
  decoding. Rule order matters only for the deterministic executable strategy; the relation still uses
  the same six coarse protocol rules.
-/
import CordialMiners.Runtime.Encode
import MeTTaILProofs.ACMatch

namespace CordialMiners.Runtime

open MeTTaIL

/-- Cordial Miners treats both state and inbox as AC collections. -/
def acOpCM (l : Label) : Bool := (l == stateOp) || (l == inboxOp)

/-- Base variable pattern. -/
def vA (name : String) : AST := .var (.base name)

/-- State collection pattern or constructor. -/
def stateA (head rest : AST) : AST := .sexp stateOp [head, rest]

/-- Inbox collection pattern or constructor. -/
def inboxA (head rest : AST) : AST := .sexp inboxOp [head, rest]

/-- Runtime configuration constructor. -/
def cmA (ib st : AST) : AST := .sexp cmOp [ib, st]

def proposeA (w h : AST) : AST := appA "propose" [w, h]
def qApproveA (w h : AST) : AST := appA "q-approve" [w, h]
def certThreshA (w h : AST) : AST := appA "cert-threshold" [w, h]
def finalA (w h : AST) : AST := appA "final" [w, h]
def finalLeaderA (w h : AST) : AST := appA "final-leader" [w, h]
def orderedPrefixPayloadA (payload : AST) : AST := appA "ordered-prefix" [payload]

def evProposeA (w h : AST) : AST := appA "ev-propose" [w, h]
def evOrderPayloadA (payload : AST) : AST := appA "ev-order" [payload]

def wVar : AST := vA "w"
def hVar : AST := vA "h"
def hsVar : AST := vA "hs"
def restVar : AST := vA "rest"
def stVar : AST := vA "st"
def ibVar : AST := vA "ib"
def ibRestVar : AST := vA "ibrest"

/-- Build a named base rewrite declaration. -/
def baseDecl (name : String) (lhs rhs : AST) : RewriteDecl :=
  ⟨name, .base lhs rhs⟩

/-- Consume a proposal event and add the corresponding `propose` fact. -/
def proposeRule : RewriteDecl :=
  baseDecl "cm-propose"
    (cmA (inboxA (evProposeA wVar hVar) ibRestVar) stVar)
    (cmA ibRestVar (stateA (proposeA wVar hVar) stVar))

/-- A proposal fact enables a quorum-approval fact. -/
def qapproveRule : RewriteDecl :=
  baseDecl "cm-qapprove"
    (cmA ibVar (stateA (proposeA wVar hVar) restVar))
    (cmA ibVar (stateA (qApproveA wVar hVar) (stateA (proposeA wVar hVar) restVar)))

/-- A quorum-approval fact enables a threshold-certificate fact. -/
def certifyRule : RewriteDecl :=
  baseDecl "cm-certify"
    (cmA ibVar (stateA (qApproveA wVar hVar) restVar))
    (cmA ibVar (stateA (certThreshA wVar hVar) (stateA (qApproveA wVar hVar) restVar)))

/-- A threshold-certificate fact enables a finality fact. -/
def finalizeRule : RewriteDecl :=
  baseDecl "cm-finalize"
    (cmA ibVar (stateA (certThreshA wVar hVar) restVar))
    (cmA ibVar (stateA (finalA wVar hVar) (stateA (certThreshA wVar hVar) restVar)))

/-- A finality fact enables the final-leader fact. -/
def finalLeadRule : RewriteDecl :=
  baseDecl "cm-final-leader"
    (cmA ibVar (stateA (finalA wVar hVar) restVar))
    (cmA ibVar (stateA (finalLeaderA wVar hVar) (stateA (finalA wVar hVar) restVar)))

/-- Consume an ordering event and add an ordered-prefix fact. The event payload is one AST list term. -/
def orderRule : RewriteDecl :=
  baseDecl "cm-order"
    (cmA (inboxA (evOrderPayloadA hsVar) ibRestVar) stVar)
    (cmA ibRestVar (stateA (orderedPrefixPayloadA hsVar) stVar))

/-- The Cordial Miners runtime presentation. Exports, terms, equations, and references are not needed by
    the current engine; it reads the rewrite declarations. -/
def cmPresentation : Presentation :=
  .mk [] [] [] [proposeRule, orderRule, finalLeadRule, finalizeRule, certifyRule, qapproveRule] []

end CordialMiners.Runtime
