-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Operational
Layer: Operational
Purpose: Aggregator for the Meta-MeTTa operational semantics (Meredith, Goertzel, Warrell and
  Vandervorst, "Meta-MeTTa: an operational semantics for MeTTa", arXiv 2305.17218), the published
  four-register abstract machine ⟨input, knowledge base, workspace, output⟩ that the authors intend
  as MeTTa's independent specification. The model is a distinct artifact from the minimal-MeTTa
  interpreter: the kernel runs programs, whereas this small-step spec reasons about program
  equivalence and resource bounds. Both are computable and share the `Core` object language.
  Importing this module pulls in the state, semantics, minimal instructions, traces, bisimulation,
  the checked coverage examples, the gas extension, and the verified properties.
Imports: MettaHyperonFull.Operational.{State, Semantics, Minimal, Trace, Bisimulation,
  SemanticsCoverage, MinimalCoverage, ResourceBounded, Properties}
Trusted boundary: none
Main exports: re-exports the Operational submodules (no new declarations)
Open obligations: none
-/
import MettaHyperonFull.Operational.State
import MettaHyperonFull.Operational.Semantics
import MettaHyperonFull.Operational.SemanticsCoverage
import MettaHyperonFull.Operational.Minimal
import MettaHyperonFull.Operational.MinimalCoverage
import MettaHyperonFull.Operational.Trace
import MettaHyperonFull.Operational.Bisimulation
import MettaHyperonFull.Operational.ResourceBounded
import MettaHyperonFull.Operational.Properties
