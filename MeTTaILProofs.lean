/-
The Mathlib-backed metatheory of MeTTaIL: decidable equality of the data model, the presentation
lattice laws, and proofs about elaboration, transformations, and reduction.
-/
-- Decidable equality and LawfulBEq for the whole data model.
import MeTTaILProofs.DecEq
-- The mq-calculus (communication = measurement): Born-rule probability conservation.
import MeTTaILProofs.MQCalculus
-- Elaboration / transformation pipeline invariants.
import MeTTaILProofs.Pipeline
-- Church-Rosser / confluence for SKI combinatory logic.
import MeTTaILProofs.SKIConfluence
-- DecEq / LambdaConfluence are added as their modules land.

