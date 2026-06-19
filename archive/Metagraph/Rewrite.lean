import MettaHyperonFull.Metagraph.SPO
import MettaHyperonFull.Metagraph.DPO

namespace Metta

inductive RewriteKind where | spo | dpo deriving Repr, BEq

structure MGRewrite where
  kind : RewriteKind
  before : Metagraph
  after : Metagraph
  deriving Repr

/-- A metagraph rewrite trace used by reflection and Ruliad modules. -/
abbrev MGTrace := List MGRewrite

end Metta
