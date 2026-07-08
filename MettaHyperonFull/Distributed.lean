-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Distributed
Layer: Distributed
Purpose: Aggregator for active distributed atomspace semantics. This layer is separate from
  Cordial Miners consensus: it models replica-local atom storage, mutation delivery, quiescence, and
  convergence boundaries for DAS-style atomspaces.
Imports: MettaHyperonFull.Distributed.DAS, MettaHyperonFull.Distributed.AxiomAudit
Trusted boundary: none
Main exports: re-exports of distributed atomspace definitions and audit checks
Open obligations: directional happens-before and unordered CRDT quotient convergence.
-/
import MettaHyperonFull.Distributed.DAS
import MettaHyperonFull.Distributed.AxiomAudit
