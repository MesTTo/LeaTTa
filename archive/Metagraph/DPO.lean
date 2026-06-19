import MettaHyperonFull.Metagraph.Homomorphism

namespace Metta

/-- Double-pushout production with interface graph K. -/
structure DPORule where
  lhs : Metagraph
  interface : Metagraph
  rhs : Metagraph

/-- Dangling condition approximation: no retained edge points to a deleted id. -/
def dpoDanglingOk (host : Metagraph) (deleted : List Nat) : Bool :=
  host.edges.all (fun e => !(e.targets.any (fun t => deleted.any (fun d => d == t))))

/-- DPO rewrite approximation: only performs when dangling condition is satisfied. -/
def applyDPOApprox (r : DPORule) (host : Metagraph) : Option Metagraph :=
  let interfaceIds := r.interface.ids
  let deleted := r.lhs.ids.filter (fun i => !(interfaceIds.any (fun k => k == i)))
  if dpoDanglingOk host deleted then
    let kept := host.edges.filter (fun e => !(deleted.any (fun i => i == e.id)))
    let added := r.rhs.edges.filter (fun e => !(interfaceIds.any (fun i => i == e.id)))
    some ⟨added ++ kept⟩
  else none

end Metta
