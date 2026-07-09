-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.QueryBackend
Layer: Proofs
Purpose: First laws for the backend-neutral query interface. The list-backed `Space` refines itself,
  conjunctive query is the serial scalar-query join, and the generated reference backend records the
  cache-invalidation generation boundary needed by MORK-style runtimes.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none
Main exports: QueryBackend.serialQueryMultiRows_nil, QueryBackend.spaceBackend_refines_self,
  QueryBackend.spaceBackend_uses_serial_queryMulti,
  QueryBackend.versionedSpaceBackend_refines_space,
  QueryBackend.versionedSpaceBackend_uses_serial_queryMulti,
  QueryBackend.versionedSpaceBackend_add_generation,
  QueryBackend.versionedSpaceBackend_removeOne_generation
Open obligations: codec, prepared-query, sharded-query, named-space, and MM2 exec laws are later
  layers over this interface.
-/
import MettaHyperonFull.Proofs.Basic
import MettaHyperonFull.Proofs.Substitution
import MettaHyperonFull.Core.QueryBackend

namespace Metta

namespace QueryBackend

/-- Empty conjunctive query has the empty binding as its single row. -/
theorem serialQueryMultiRows_nil (scalar : Atom → List Bindings) :
    serialQueryMultiRows scalar [] = [Bindings.empty] := rfl

/-- Empty conjunctive query packaged with its observed generation. -/
theorem serialQueryMulti_nil (generation : Nat) (scalar : Atom → List Bindings) :
    serialQueryMulti generation scalar [] =
      QueryResult.completeAt generation [Bindings.empty] := rfl

/-- The list-backed backend has exactly the scalar-query rows of `Space.query`. -/
theorem spaceBackend_refines_self (s : Space) :
    RefinesSpace spaceBackend s s := by
  intro _pattern
  rfl

/-- The list-backed backend's conjunctive query is the serial scalar-query join. -/
theorem spaceBackend_uses_serial_queryMulti :
    UsesSerialQueryMulti spaceBackend := by
  intro _state _patterns
  rfl

/-- The list-backed backend does not advance generations. -/
theorem spaceBackend_query_generation (s : Space) (pattern : Atom) :
    (spaceBackend.query s pattern).generation = 0 := rfl

/-- The generated reference backend has the scalar-query rows of its inner `Space`. -/
theorem versionedSpaceBackend_refines_space (s : VersionedSpace) :
    RefinesSpace versionedSpaceBackend s s.space := by
  intro _pattern
  rfl

/-- The generated reference backend's conjunctive query is the serial scalar-query join. -/
theorem versionedSpaceBackend_uses_serial_queryMulti :
    UsesSerialQueryMulti versionedSpaceBackend := by
  intro _state _patterns
  rfl

/-- Scalar queries on the generated reference backend report the current generation. -/
theorem versionedSpaceBackend_query_generation (s : VersionedSpace) (pattern : Atom) :
    (versionedSpaceBackend.query s pattern).generation = s.generation := rfl

/-- Adding an atom advances the generation stamp once. -/
theorem versionedSpaceBackend_add_generation (s : VersionedSpace) (a : Atom) :
    (versionedSpaceBackend.add s a).generation = s.generation + 1 := rfl

/-- Removing one atom copy advances the generation stamp once. -/
theorem versionedSpaceBackend_removeOne_generation (s : VersionedSpace) (a : Atom) :
    (versionedSpaceBackend.removeOne s a).generation = s.generation + 1 := rfl

/-- Adding through the generated backend refines list-backed insertion. -/
theorem versionedSpaceBackend_add_refines_insert (s : VersionedSpace) (a : Atom) :
    (versionedSpaceBackend.add s a).space = s.space.insert a := rfl

/-- Removing through the generated backend refines one-copy list-backed removal. -/
theorem versionedSpaceBackend_removeOne_refines_removeOne (s : VersionedSpace) (a : Atom) :
    (versionedSpaceBackend.removeOne s a).space = s.space.removeOne a := rfl

end QueryBackend

private def edgeAB : Atom :=
  Atom.expr [Atom.sym "edge", Atom.sym "a", Atom.sym "b"]

private def edgeBC : Atom :=
  Atom.expr [Atom.sym "edge", Atom.sym "b", Atom.sym "c"]

private def edgeSpace : Space :=
  ⟨[edgeAB, edgeBC]⟩

private def edgeAto : Atom :=
  Atom.expr [Atom.sym "edge", Atom.sym "a", Atom.var "to"]

private def edgeAMid : Atom :=
  Atom.expr [Atom.sym "edge", Atom.sym "a", Atom.var "mid"]

private def edgeMidTo : Atom :=
  Atom.expr [Atom.sym "edge", Atom.var "mid", Atom.var "to"]

private def edgeBTo : Atom :=
  Atom.expr [Atom.sym "edge", Atom.sym "b", Atom.var "to"]

private theorem match_edgeAto_edgeAB :
    matchAtoms edgeAto edgeAB = [[BindingRel.val "to" (Atom.sym "b")]] := by
  simp [edgeAto, edgeAB, matchAtoms, matchAtomsWith, matchAll, Bindings.merge, Bindings.mergeOne,
    Bindings.addVarBinding, Bindings.lookupVal, Bindings.addValRaw, Bindings.removeVal,
    Subst.occurs]

private theorem match_edgeAto_edgeBC :
    matchAtoms edgeAto edgeBC = [] := by
  simp [edgeAto, edgeBC, matchAtoms, matchAtomsWith, matchAll, Bindings.merge, Bindings.mergeOne,
    Bindings.addVarBinding, Bindings.addValRaw, Bindings.removeVal, Subst.occurs]

private theorem edgeAto_rows :
    edgeSpace.query edgeAto = [[BindingRel.val "to" (Atom.sym "b")]] := by
  simp [Space.query, edgeSpace, match_edgeAto_edgeAB, match_edgeAto_edgeBC]

private theorem match_edgeAMid_edgeAB :
    matchAtoms edgeAMid edgeAB = [[BindingRel.val "mid" (Atom.sym "b")]] := by
  simp [edgeAMid, edgeAB, matchAtoms, matchAtomsWith, matchAll, Bindings.merge, Bindings.mergeOne,
    Bindings.addVarBinding, Bindings.lookupVal, Bindings.addValRaw, Bindings.removeVal,
    Subst.occurs]

private theorem match_edgeAMid_edgeBC :
    matchAtoms edgeAMid edgeBC = [] := by
  simp [edgeAMid, edgeBC, matchAtoms, matchAtomsWith, matchAll, Bindings.merge, Bindings.mergeOne,
    Bindings.addVarBinding, Bindings.addValRaw, Bindings.removeVal, Subst.occurs]

private theorem edgeAMid_rows :
    edgeSpace.query edgeAMid = [[BindingRel.val "mid" (Atom.sym "b")]] := by
  simp [Space.query, edgeSpace, match_edgeAMid_edgeAB, match_edgeAMid_edgeBC]

private theorem match_edgeBTo_edgeAB :
    matchAtoms edgeBTo edgeAB = [] := by
  simp [edgeBTo, edgeAB, matchAtoms, matchAtomsWith, matchAll, Bindings.merge, Bindings.mergeOne,
    Bindings.addVarBinding, Bindings.addValRaw, Bindings.removeVal, Subst.occurs]

private theorem match_edgeBTo_edgeBC :
    matchAtoms edgeBTo edgeBC = [[BindingRel.val "to" (Atom.sym "c")]] := by
  simp [edgeBTo, edgeBC, matchAtoms, matchAtomsWith, matchAll, Bindings.merge, Bindings.mergeOne,
    Bindings.addVarBinding, Bindings.lookupVal, Bindings.addValRaw, Bindings.removeVal,
    Subst.occurs]

private theorem edgeBTo_rows :
    edgeSpace.query edgeBTo = [[BindingRel.val "to" (Atom.sym "c")]] := by
  simp [Space.query, edgeSpace, match_edgeBTo_edgeAB, match_edgeBTo_edgeBC]

private theorem empty_merge_mid :
    Bindings.merge Bindings.empty [BindingRel.val "mid" (Atom.sym "b")] =
      [[BindingRel.val "mid" (Atom.sym "b")]] := by
  rfl

private theorem instantiate_mid_row_edgeMidTo :
    instantiate [BindingRel.val "mid" (Atom.sym "b")] edgeMidTo = edgeBTo := by
  simp [instantiate, bindingsToSubst, Subst.apply, Subst.lookup, edgeMidTo, edgeBTo]

private theorem mid_merge_to :
    Bindings.merge [BindingRel.val "mid" (Atom.sym "b")] [BindingRel.val "to" (Atom.sym "c")] =
      [[BindingRel.val "to" (Atom.sym "c"), BindingRel.val "mid" (Atom.sym "b")]] := by
  rfl

/-- Scalar query finds the expected row in the reference backend. -/
example :
    (QueryBackend.spaceBackend.query edgeSpace edgeAto).rows =
      [[BindingRel.val "to" (Atom.sym "b")]] := by
  simpa [QueryBackend.spaceBackend, QueryResult.completeAt] using edgeAto_rows

/-- Conjunctive query instantiates later patterns with earlier rows and merges the result. -/
example :
    (QueryBackend.spaceBackend.queryMulti edgeSpace [edgeAMid, edgeMidTo]).rows =
      [[BindingRel.val "to" (Atom.sym "c"), BindingRel.val "mid" (Atom.sym "b")]] := by
  simp [QueryBackend.spaceBackend, QueryBackend.serialQueryMulti, QueryBackend.serialQueryMultiRows,
    QueryResult.completeAt]
  rw [show instantiate Bindings.empty edgeAMid = edgeAMid by
    simpa [Bindings.empty] using instantiate_nil edgeAMid]
  rw [edgeAMid_rows]
  simp [empty_merge_mid]
  rw [instantiate_mid_row_edgeMidTo]
  rw [edgeBTo_rows]
  simp [mid_merge_to]

end Metta
