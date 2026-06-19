import MettaHyperonFull.Runtime.Program

namespace Metta

/-- A conformance test compares this Lean runtime against an external Hyperon executable. -/
structure ConformanceCase where
  name : String
  source : String
  expectedAtoms : List Atom
  deriving Repr, Inhabited

/-- Executable Lean-side checker. -/
def runConformanceLean (c : ConformanceCase) : Bool :=
  match Runtime.runProgramString {} c.source with
  | Except.ok r => r.final.output.atoms == c.expectedAtoms
  | _ => false

end Metta
