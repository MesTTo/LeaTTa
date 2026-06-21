/-
Module: CordialMiners.Extract.MettaIL
Layer: Extract
Purpose: Extraction of the coarse protocol facts to MeTTaIL atoms, and the proof that it loses nothing.
  encodeFact compiles each fact to an S-expression (a head symbol plus its encoded fields); decodeFact
  parses one back. The round-trip theorem extract_decode_encode shows that decoding an encoded fact
  recovers it exactly, given left-inverse field codecs. Extraction is therefore lossless: every coarse
  fact has a faithful MeTTaIL image that the parser maps back to the original.
Imports: CordialMiners.CMIR.Atom, CordialMiners.Trec.Syntax
Trusted boundary: none (fully proved)
Main exports: encodeFact, decodeFact, extract_decode_encode
Open obligations: none
-/
import CordialMiners.CMIR.Atom
import CordialMiners.Trec.Syntax

namespace CordialMiners

variable {Wave Hash : Type*}

/-- Encode a coarse fact as a MeTTaIL atom: a head symbol naming the fact, followed by its encoded
    fields. The ordered prefix is encoded as the head symbol consed onto the encoded hash list. -/
def encodeFact (eW : Wave → Sexpr) (eH : Hash → Sexpr) : TrecFact Wave Hash → Sexpr
  | .propose w h => .app [.sym "propose", eW w, eH h]
  | .qApprove w h => .app [.sym "q-approve", eW w, eH h]
  | .certThresh w h => .app [.sym "cert-threshold", eW w, eH h]
  | .final w h => .app [.sym "final", eW w, eH h]
  | .finalLeader w h => .app [.sym "final-leader", eW w, eH h]
  | .orderedPrefix hs => .app (.sym "ordered-prefix" :: hs.map eH)

/-- Parse a MeTTaIL atom back into a coarse fact, matching on the head symbol and field arity. Anything
    that does not match a known shape decodes to `none`. -/
def decodeFact (dW : Sexpr → Option Wave) (dH : Sexpr → Option Hash) :
    Sexpr → Option (TrecFact Wave Hash)
  | .app [.sym "propose", a, b] =>
      match dW a, dH b with
      | some w, some h => some (.propose w h)
      | _, _ => none
  | .app [.sym "q-approve", a, b] =>
      match dW a, dH b with
      | some w, some h => some (.qApprove w h)
      | _, _ => none
  | .app [.sym "cert-threshold", a, b] =>
      match dW a, dH b with
      | some w, some h => some (.certThresh w h)
      | _, _ => none
  | .app [.sym "final", a, b] =>
      match dW a, dH b with
      | some w, some h => some (.final w h)
      | _, _ => none
  | .app [.sym "final-leader", a, b] =>
      match dW a, dH b with
      | some w, some h => some (.finalLeader w h)
      | _, _ => none
  | .app (.sym "ordered-prefix" :: rest) => (rest.mapM dH).map TrecFact.orderedPrefix
  | _ => none

/-- A list of encoded items decodes back to the original list, given a field codec that is a left
    inverse. The list mirror of the round-trip property. -/
theorem mapM_map_leftInv (e : Hash → Sexpr) (d : Sexpr → Option Hash)
    (hd : ∀ a, d (e a) = some a) : ∀ l : List Hash, (l.map e).mapM d = some l := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, hd, ih]

/-- Extraction is lossless: decoding an encoded fact recovers it exactly, provided the field codecs are
    left inverses (`dW (eW w) = some w` and `dH (eH h) = some h`). Every coarse fact therefore has a
    faithful MeTTaIL image. -/
theorem extract_decode_encode (eW : Wave → Sexpr) (eH : Hash → Sexpr)
    (dW : Sexpr → Option Wave) (dH : Sexpr → Option Hash)
    (hW : ∀ w, dW (eW w) = some w) (hH : ∀ h, dH (eH h) = some h) :
    ∀ f : TrecFact Wave Hash, decodeFact dW dH (encodeFact eW eH f) = some f := by
  intro f
  cases f with
  | propose w h => simp [encodeFact, decodeFact, hW, hH]
  | qApprove w h => simp [encodeFact, decodeFact, hW, hH]
  | certThresh w h => simp [encodeFact, decodeFact, hW, hH]
  | final w h => simp [encodeFact, decodeFact, hW, hH]
  | finalLeader w h => simp [encodeFact, decodeFact, hW, hH]
  | orderedPrefix hs => simp [encodeFact, decodeFact, mapM_map_leftInv eH dH hH hs]

end CordialMiners
