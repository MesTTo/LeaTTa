/-
Module: MeTTaILProofs
Layer: Library root
Purpose: The root of the Mathlib-backed metatheory of MeTTaIL. It aggregates decidable equality of
  the data model, the mq-calculus probability results, the elaboration and transformation pipeline
  invariants, the presentation lattice laws, and Church-Rosser confluence for SKI combinatory logic
  and for beta reduction of the lambda calculus.
Imports: the MeTTaILProofs modules (DecEq, MQCalculus, Pipeline, Lattice, SKIConfluence,
  LambdaConfluence)
Trusted boundary: none
Main exports: (aggregator; re-exports the library)
Open obligations: none
-/
-- Decidable equality and LawfulBEq for the whole data model.
import MeTTaILProofs.DecEq
-- The mq-calculus (communication = measurement): Born-rule probability conservation.
import MeTTaILProofs.MQCalculus
-- Elaboration / transformation pipeline invariants.
import MeTTaILProofs.Pipeline
-- The presentation lattice laws (union / intersection / difference as set operations).
import MeTTaILProofs.Lattice
-- Church-Rosser / confluence for SKI combinatory logic.
import MeTTaILProofs.SKIConfluence
-- Church-Rosser / confluence of beta reduction for the lambda calculus.
import MeTTaILProofs.LambdaConfluence

