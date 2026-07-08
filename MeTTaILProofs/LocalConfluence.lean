-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.LocalConfluence
Layer: Proofs
Purpose: The disjoint-redex case of local confluence, the structural foundation of Huet's Critical Pair
  Theorem. That theorem (a terminating term rewriting system is confluent iff all its critical pairs are
  joinable) splits a divergence `t1 <- t0 -> t2` into three cases: the two redexes are in disjoint
  subtrees (always joinable), one is below a variable position of the other (joinable), or the left-hand
  sides overlap at a non-variable position (a critical pair, joinable by assumption). Here the disjoint
  case is formalized for `RewStep`: two steps in different arguments of a `sexp`, or in the two components
  of a `Subst`, always commute, giving a joinable diamond. With `MeTTaILProofs.Newman` this is the part of
  local confluence that holds with no side-condition; the overlap cases (critical pairs computed by
  unification, Case 2 of the theorem) are the remaining piece, and the abstract treatment of critical
  pairs for relations with context operators (Haemmerlé and Fages, RTA 2007) is the route to them.
Imports: MeTTaILProofs.Newman (Joinable, Confluent), MeTTaIL.Semantics.Context (RewStep)
Trusted boundary: none (fully proved)
Main exports: joinable_substB_substR, joinable_args_disjoint
Open obligations: the overlap cases of the Critical Pair Theorem (Cases 2.1 and 2.2) need positions,
  unification, and critical-pair computation; they are future work.
-/
import MeTTaILProofs.Newman
import MeTTaIL.Semantics.Context

namespace MeTTaIL

open Relation

/-- Disjoint redexes in the two components of a `Subst` commute: a step in the body and a step in the
    replacement are joinable, with the common reduct obtained by doing the other step. The Subst case of
    "disjoint redexes are joinable" (Critical Pair Theorem, Case 1). -/
theorem joinable_substB_substR (p : Presentation) {b b' r r' : AST} {v : DottedPath}
    (hb : RewStep p b b') (hr : RewStep p r r') :
    Joinable (RewStep p) (.subst b' r v) (.subst b r' v) :=
  ⟨.subst b' r' v,
    ReflTransGen.single (RewStep.substR hr),
    ReflTransGen.single (RewStep.substB hb)⟩

/-- Disjoint redexes in two different arguments of a `sexp` commute: reducing the argument before the
    middle segment and the argument after it are joinable, with the common reduct obtained by doing both.
    The `sexp`-context case of "disjoint redexes are joinable" (Critical Pair Theorem, Case 1). -/
theorem joinable_args_disjoint (p : Presentation) (l : Label) {a a' b b' : AST}
    (pre mid post : List AST) (ha : RewStep p a a') (hb : RewStep p b b') :
    Joinable (RewStep p)
      (.sexp l (pre ++ a' :: mid ++ b :: post)) (.sexp l (pre ++ a :: mid ++ b' :: post)) := by
  refine ⟨.sexp l (pre ++ a' :: mid ++ b' :: post), ?_, ?_⟩
  · have h := RewStep.arg (p := p) (l := l) (pre := pre ++ a' :: mid) (post := post) hb
    exact ReflTransGen.single (by simpa using h)
  · have h := RewStep.arg (p := p) (l := l) (pre := pre) (post := mid ++ b' :: post) ha
    exact ReflTransGen.single (by simpa using h)

end MeTTaIL
