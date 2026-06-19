import MettaHyperonFull.Metagraph.Basic
import MettaHyperonFull.Core.Types

namespace Metta

/-- Enrichment homomorphism `Ψ`: maps the enrichment label of a metagraph edge to the
    enrichment of its image. The identity map is the default when no structured
    homomorphism on the enrichment algebra is available. -/
structure EnrichmentHom where
  map : Atom → Atom

/-- The identity enrichment homomorphism. -/
def EnrichmentHom.id : EnrichmentHom := ⟨fun a => a⟩

/-- A metagraph homomorphism `Φ` maps edge ids while respecting label symbols, type
    inheritance (`T' < T`, i.e. the image type is a subtype), and the enrichment
    homomorphism (`S' = Ψ(S)`), as in arXiv:2112.08272 §3.2. -/
structure MGHom (env : TypeEnv) (src tgt : Metagraph) where
  edgeMap : Nat → Nat
  enrich : EnrichmentHom
  labelOk : ∀ e ∈ src.edges,
    match tgt.findEdge? (edgeMap e.id) with
    | some e' =>
        e'.label.symbol = e.label.symbol ∧
        (match e.label.ty, e'.label.ty with
         | none, _ => True
         | some ty, some ty' => TypeEnv.inherits env ty' ty = true
         | some _, none => False) ∧
        (match e.label.enrichment with
         | none => True
         | some s => e'.label.enrichment = some (enrich.map s))
    | none => False

/-- Pattern match as homomorphism. -/
abbrev MGMatches (env : TypeEnv) (pattern host : Metagraph) := MGHom env pattern host

end Metta
