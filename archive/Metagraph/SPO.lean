import MettaHyperonFull.Metagraph.Homomorphism

namespace Metta

/-- Single-pushout style graph/metagraph rewrite rule. `preserve` maps ids retained from L to R. -/
structure SPORule where
  lhs : Metagraph
  rhs : Metagraph
  preserve : Nat → Option Nat

/-- A record of a single SPO direct derivation. `SPORule` carries a function field
    (`preserve`), so this structure is not `Repr`/`BEq`-derivable. -/
structure SPODerivation where
  rule : SPORule
  host : Metagraph
  result : Metagraph
  deleted : List Nat
  added : List MGEdge

/-- Executable approximation of SPO rewrite: remove matched lhs ids not preserved and add rhs ids not in image. -/
def applySPOApprox (r : SPORule) (host : Metagraph) : Metagraph :=
  let preservedTargets := r.lhs.ids.filterMap r.preserve
  let deleted := r.lhs.ids.filter (fun i => (r.preserve i).isNone)
  let kept := host.edges.filter (fun e => !(deleted.any (fun i => i == e.id)))
  let added := r.rhs.edges.filter (fun e => !(preservedTargets.any (fun i => i == e.id)))
  ⟨added ++ kept⟩

end Metta
