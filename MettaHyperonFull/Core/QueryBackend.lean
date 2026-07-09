-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.QueryBackend
Layer: Core
Purpose: A backend-neutral query surface for MeTTa spaces. It keeps `Space` as the executable
  reference backend while naming the operations a MORK-backed implementation must refine: scalar
  query, conjunctive query, mutation, snapshots, and generation stamps for cache validation.
Imports: MettaHyperonFull.Core.Space
Trusted boundary: none
Main exports: Capabilities, QueryResult, QueryBackend, QueryBackend.serialQueryMultiRows,
  QueryBackend.serialQueryMulti, QueryBackend.RefinesSpace, QueryBackend.UsesSerialQueryMulti,
  QueryBackend.spaceBackend, VersionedSpace, QueryBackend.versionedSpaceBackend
Open obligations: codec refinement, transaction laws, prepared-query equivalence, and sharding laws
  are stated in the roadmap and live above this core interface.
-/
import MettaHyperonFull.Core.Space

namespace Metta

/-- Runtime features exposed by a query backend. The fields are data, not trusted assumptions. -/
structure Capabilities where
  scalarQuery : Bool := true
  queryMulti : Bool := true
  transactions : Bool := false
  generations : Bool := false
  streaming : Bool := false
  deriving BEq, Inhabited, Repr

namespace Capabilities

/-- The reference `Space` backend supports scalar and conjunctive query only. -/
def scalarAndJoin : Capabilities :=
  { scalarQuery := true
    queryMulti := true
    transactions := false
    generations := false
    streaming := false }

/-- A scalar-and-join backend whose mutations advance a generation stamp. -/
def generatedScalarAndJoin : Capabilities :=
  { scalarAndJoin with generations := true }

end Capabilities

/-- A query result carries rows plus the generation observed by the query. -/
structure QueryResult where
  generation : Nat
  rows : List Bindings
  complete : Bool := true
  deriving BEq, Inhabited, Repr

namespace QueryResult

/-- Build a complete query result at one generation. -/
def completeAt (generation : Nat) (rows : List Bindings) : QueryResult :=
  { generation, rows, complete := true }

end QueryResult

/-- A MeTTa query backend with a concrete mutable state type. -/
structure QueryBackend where
  State : Type
  capabilities : Capabilities
  generation : State → Nat
  query : State → Atom → QueryResult
  queryMulti : State → List Atom → QueryResult
  add : State → Atom → State
  removeOne : State → Atom → State
  snapshot : State → State
  restore : State → State → State

namespace QueryBackend

/-- Conjunctive query as serial scalar queries with seed instantiation and binding merge. -/
def serialQueryMultiRows (scalar : Atom → List Bindings) (patterns : List Atom) : List Bindings :=
  patterns.foldl
    (fun rows pattern =>
      rows.flatMap (fun seed =>
        (scalar (instantiate seed pattern)).flatMap (fun row =>
          Bindings.merge seed row)))
    [Bindings.empty]

/-- `serialQueryMultiRows` packaged as a complete query result. -/
def serialQueryMulti (generation : Nat) (scalar : Atom → List Bindings)
    (patterns : List Atom) : QueryResult :=
  QueryResult.completeAt generation (serialQueryMultiRows scalar patterns)

/-- Backend `B` has the same scalar-query rows as the list-backed reference space. -/
def RefinesSpace (B : QueryBackend) (state : B.State) (space : Space) : Prop :=
  ∀ pattern, (B.query state pattern).rows = space.query pattern

/-- Backend `B` implements conjunctive query by the serial scalar-query join. -/
def UsesSerialQueryMulti (B : QueryBackend) : Prop :=
  ∀ state patterns,
    B.queryMulti state patterns =
      serialQueryMulti (B.generation state) (fun pattern => (B.query state pattern).rows) patterns

/-- The current list-backed `Space` as the reference query backend. -/
def spaceBackend : QueryBackend where
  State := Space
  capabilities := Capabilities.scalarAndJoin
  generation := fun _ => 0
  query := fun s pattern => QueryResult.completeAt 0 (s.query pattern)
  queryMulti := fun s patterns => serialQueryMulti 0 (fun pattern => s.query pattern) patterns
  add := Space.insert
  removeOne := Space.removeOne
  snapshot := id
  restore := fun snap _ => snap

end QueryBackend

/-- A list-backed space with a mutation generation stamp for cache laws. -/
structure VersionedSpace where
  space : Space
  generation : Nat
  deriving BEq, Inhabited, Repr

namespace VersionedSpace

def empty : VersionedSpace :=
  { space := Space.empty, generation := 0 }

def query (s : VersionedSpace) (pattern : Atom) : List Bindings :=
  s.space.query pattern

def queryMulti (s : VersionedSpace) (patterns : List Atom) : QueryResult :=
  QueryBackend.serialQueryMulti s.generation (fun pattern => s.query pattern) patterns

/-- Add an atom and advance the generation used by cache validation. -/
def add (s : VersionedSpace) (a : Atom) : VersionedSpace :=
  { space := s.space.insert a, generation := s.generation + 1 }

/-- Remove one atom copy and advance the generation used by cache validation. -/
def removeOne (s : VersionedSpace) (a : Atom) : VersionedSpace :=
  { space := s.space.removeOne a, generation := s.generation + 1 }

end VersionedSpace

namespace QueryBackend

/-- A generated reference backend used to state cache-invalidation laws before MORK enters Lean. -/
def versionedSpaceBackend : QueryBackend where
  State := VersionedSpace
  capabilities := Capabilities.generatedScalarAndJoin
  generation := VersionedSpace.generation
  query := fun s pattern => QueryResult.completeAt s.generation (s.query pattern)
  queryMulti := VersionedSpace.queryMulti
  add := VersionedSpace.add
  removeOne := VersionedSpace.removeOne
  snapshot := id
  restore := fun snap _ => snap

end QueryBackend

end Metta
