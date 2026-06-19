import MettaHyperonFull.Core.Space

namespace Metta

structure Module where
  name : String
  space : Space
  imports : List String := []
  deriving Repr, BEq, Inhabited

structure ModuleCatalog where
  modules : List Module
  deriving Repr, Inhabited

namespace ModuleCatalog

def lookup (c : ModuleCatalog) (n : String) : Option Module := c.modules.find? (fun m => m.name == n)
def register (c : ModuleCatalog) (m : Module) : ModuleCatalog := { c with modules := m :: c.modules }

def moduleSpaceNoDeps (c : ModuleCatalog) (n : String) : Option Space := (lookup c n).map (fun m => m.space)

def mergedSpace (c : ModuleCatalog) (n : String) : Option Space :=
  match lookup c n with
  | none => none
  | some m =>
      let depSpaces := m.imports.filterMap (fun i => (lookup c i).map (fun mm => mm.space))
      some (depSpaces.foldl Space.append m.space)

end ModuleCatalog

end Metta
