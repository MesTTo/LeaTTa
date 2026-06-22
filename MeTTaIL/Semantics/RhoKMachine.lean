/-
Module: MeTTaIL.Semantics.RhoKMachine
Layer: Semantics
Purpose: A K-shaped operational layer for the rho target. The local `f1r3node` K semantics stores
  sends and receives in `<Out>` and `<In>` cells, checks a match, keeps persistent receives installed,
  and then spawns the substituted body. This file records that persistent-receive step as a checked
  machine step and proves that it reifies to the rho COMM relation modulo structural congruence.
Imports: MeTTaIL.Semantics.Rho
Trusted boundary: none
Main exports: Rho.KMachine.InCell, Rho.KMachine.OutCell, Rho.KMachine.Config,
  Rho.KMachine.Step, Rho.KMachine.step_to_rho
Open obligations: add ordinary receives, persistent sends, persistent/persistent loops, candidate-ID
  bookkeeping, arity and pattern matching, and the full correspondence with the K configuration rules.
-/
import MeTTaIL.Semantics.Rho

namespace MeTTaIL
namespace Rho
namespace KMachine

/-- A K-style receive cell. The checked step below uses `persistent = true`. -/
structure InCell where
  chan : Name
  binder : String
  body : Proc
  persistent : Bool

/-- A K-style output cell. Ordinary outputs have `persistent = false`. -/
structure OutCell where
  chan : Name
  msg : Proc
  persistent : Bool

/-- A small K-shaped configuration: waiting receives, waiting outputs, and spawned processes. -/
structure Config where
  inputs : List InCell
  outputs : List OutCell
  threads : List Proc

/-- Reify a receive cell as the persistent listener process used by the rho fragment. -/
def InCell.toProc (cell : InCell) : Proc :=
  .input cell.chan cell.binder cell.body

/-- Reify an output cell as a rho output process. -/
def OutCell.toProc (cell : OutCell) : Proc :=
  .out cell.chan cell.msg

/-- Reify a K-shaped configuration as a rho process by running all cells and threads in parallel. -/
def Config.toProc (cfg : Config) : Proc :=
  parList (cfg.inputs.map InCell.toProc ++ cfg.outputs.map OutCell.toProc ++ cfg.threads)

/-- The one-cell source configuration for persistent receive firing. -/
def receiveSource (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := [output]
  threads := []

/-- The one-cell target configuration after the output was consumed and the input stayed installed. -/
def receiveTarget (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := []
  threads := [substProc input.binder (.quote output.msg) input.body]

/-- K-machine steps currently checked against rho. This is the persistent receive branch from
    `persistent-sending-receiving.k`. -/
inductive Step : Config → Config → Prop where
  | persistentReceive {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hin : input.persistent = true)
      (hout : output.persistent = false) :
      Step (receiveSource input output) (receiveTarget input output)

/-- The K-shaped persistent receive step reifies to rho COMM modulo `|` structure. -/
theorem step_to_rho {cfg cfg' : Config} (hstep : Step cfg cfg') :
    StepModStruct cfg.toProc cfg'.toProc := by
  cases hstep
  rename_i input output hchan hin hout
  simp only [Config.toProc, receiveSource, receiveTarget, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, parList, InCell.toProc, OutCell.toProc]
  rw [hchan]
  refine ⟨
    .par (.input output.chan input.binder input.body) (.out output.chan output.msg),
    .par (.input output.chan input.binder input.body)
      (substProc input.binder (.quote output.msg) input.body),
    ?_, Step.comm, ?_⟩
  · exact StructEq.par_congr StructEq.refl StructEq.par_zero_right
  · exact StructEq.par_congr StructEq.refl (StructEq.symm StructEq.par_zero_right)

/-- The K-machine fragment as a labelled transition system. -/
def lts : Denotational.LTS Config Unit where
  step cfg _ cfg' := Step cfg cfg'

end KMachine
end Rho
end MeTTaIL
