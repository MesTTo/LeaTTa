import MettaHyperonFull.Metagraph.Rewrite
import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- Encode a MeTTa runtime state as a metagraph by placing each register under its own label. -/
def encodeSpace (base : Nat) (label : String) (s : Space) : List MGEdge :=
  let root := ⟨base, ⟨label, none, none⟩, List.range s.atoms.length |>.map (fun i => base + i + 1)⟩
  root :: s.atoms.zipIdx.map (fun (a, i) => ⟨base + i + 1, ⟨"Atom", none, some a⟩, []⟩)

def encodeState (s : State) : Metagraph :=
  ⟨encodeSpace 0 "input" s.input ++ encodeSpace 100000 "kb" s.kb ++ encodeSpace 200000 "work" s.work ++ encodeSpace 300000 "output" s.output⟩

end Metta
