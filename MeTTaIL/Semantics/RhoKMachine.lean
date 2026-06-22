/-
Module: MeTTaIL.Semantics.RhoKMachine
Layer: Semantics
Purpose: A K-shaped operational layer for the rho target. The local `f1r3node` K semantics stores
  sends and receives in `<Out>` and `<In>` cells, checks a match, consumes ordinary receives, keeps
  persistent sends and receives installed, and then spawns the substituted body. This file records the
  ordinary and persistent one-channel send/receive steps and proves that they reify to the rho COMM
  relation modulo structural congruence.
Imports: MeTTaIL.Semantics.Rho
Trusted boundary: none
Main exports: Rho.KMachine.InCell, Rho.KMachine.OutCell, Rho.KMachine.Config,
  Rho.KMachine.Step, Rho.KMachine.step_to_rho, Rho.KMachine.ordinaryReceive_to_rho,
  Rho.KMachine.persistentOutput_to_rho, Rho.KMachine.persistentReceive_to_rho,
  Rho.KMachine.persistentBoth_to_rho
Open obligations: add candidate-ID bookkeeping, arity and pattern matching, and the full correspondence
  with the K configuration rules.
-/
import MeTTaIL.Semantics.Rho

namespace MeTTaIL
namespace Rho
namespace KMachine

/-- A K-style receive cell. `persistent = false` is ordinary `<-`; `persistent = true` is `<=`. -/
structure InCell where
  chan : Name
  binder : String
  body : Proc
  persistent : Bool

/-- A K-style output cell. `persistent = false` is ordinary `!`; `persistent = true` is `!!`. -/
structure OutCell where
  chan : Name
  msg : Proc
  persistent : Bool

/-- A small K-shaped configuration: waiting receives, waiting outputs, and spawned processes. -/
structure Config where
  inputs : List InCell
  outputs : List OutCell
  threads : List Proc

/-- Reify a receive cell as ordinary or persistent rho input. -/
def InCell.toProc (cell : InCell) : Proc :=
  if cell.persistent then .input cell.chan cell.binder cell.body
  else .inputOnce cell.chan cell.binder cell.body

/-- Reify an output cell as ordinary or persistent rho output. -/
def OutCell.toProc (cell : OutCell) : Proc :=
  if cell.persistent then .outPersistent cell.chan cell.msg else .out cell.chan cell.msg

/-- Reify a K-shaped configuration as a rho process by running all cells and threads in parallel. -/
def Config.toProc (cfg : Config) : Proc :=
  parList (cfg.inputs.map InCell.toProc ++ cfg.outputs.map OutCell.toProc ++ cfg.threads)

/-- The one-cell source configuration for persistent receive firing. -/
def receiveSource (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := [output]
  threads := []

/-- The one-cell target configuration after an ordinary receive consumed the input and output. -/
def receiveOnceTarget (input : InCell) (output : OutCell) : Config where
  inputs := []
  outputs := []
  threads := [substProc input.binder (.quote output.msg) input.body]

/-- The one-cell target configuration after a persistent output fired and stayed installed. -/
def persistentOutputTarget (input : InCell) (output : OutCell) : Config where
  inputs := []
  outputs := [output]
  threads := [substProc input.binder (.quote output.msg) input.body]

/-- The one-cell target configuration after the output was consumed and the input stayed installed. -/
def receiveTarget (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := []
  threads := [substProc input.binder (.quote output.msg) input.body]

/-- The one-cell target configuration after persistent input and output both stayed installed. -/
def persistentBothTarget (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := [output]
  threads := [substProc input.binder (.quote output.msg) input.body]

/-- K-machine receive steps currently checked against rho. -/
inductive Step : Config → Config → Prop where
  | ordinaryReceive {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hin : input.persistent = false)
      (hout : output.persistent = false) :
      Step (receiveSource input output) (receiveOnceTarget input output)
  | persistentOutput {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hin : input.persistent = false)
      (hout : output.persistent = true) :
      Step (receiveSource input output) (persistentOutputTarget input output)
  | persistentReceive {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hin : input.persistent = true)
      (hout : output.persistent = false) :
      Step (receiveSource input output) (receiveTarget input output)
  | persistentBoth {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hin : input.persistent = true)
      (hout : output.persistent = true) :
      Step (receiveSource input output) (persistentBothTarget input output)

/-- K-shaped receive steps reify to rho COMM modulo `|` structure. -/
theorem step_to_rho {cfg cfg' : Config} (hstep : Step cfg cfg') :
    StepModStruct cfg.toProc cfg'.toProc := by
  cases hstep
  · rename_i input output hchan hin hout
    simp only [Config.toProc, receiveSource, receiveOnceTarget, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, parList, InCell.toProc, OutCell.toProc, hin, Bool.false_eq_true,
      hout, ↓reduceIte]
    rw [hchan]
    refine ⟨
      .par (.inputOnce output.chan input.binder input.body) (.out output.chan output.msg),
      substProc input.binder (.quote output.msg) input.body,
      ?_, Step.comm_once, ?_⟩
    · exact StructEq.par_congr StructEq.refl StructEq.par_zero_right
    · exact StructEq.symm StructEq.par_zero_right
  · rename_i input output hchan hin hout
    simp only [Config.toProc, receiveSource, persistentOutputTarget, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, parList, InCell.toProc, OutCell.toProc, hin, hout,
      Bool.false_eq_true, ↓reduceIte]
    rw [hchan]
    refine ⟨
      .par (.inputOnce output.chan input.binder input.body)
        (.outPersistent output.chan output.msg),
      .par (.outPersistent output.chan output.msg)
        (substProc input.binder (.quote output.msg) input.body),
      ?_, Step.comm_once_persistent_out, ?_⟩
    · exact StructEq.par_congr StructEq.refl StructEq.par_zero_right
    · exact StructEq.par_congr StructEq.refl (StructEq.symm StructEq.par_zero_right)
  · rename_i input output hchan hin hout
    simp only [Config.toProc, receiveSource, receiveTarget, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, parList, InCell.toProc, OutCell.toProc, hin, hout,
      ↓reduceIte]
    rw [hchan]
    refine ⟨
      .par (.input output.chan input.binder input.body) (.out output.chan output.msg),
      .par (.input output.chan input.binder input.body)
        (substProc input.binder (.quote output.msg) input.body),
      ?_, Step.comm, ?_⟩
    · exact StructEq.par_congr StructEq.refl StructEq.par_zero_right
    · exact StructEq.par_congr StructEq.refl (StructEq.symm StructEq.par_zero_right)
  · rename_i input output hchan hin hout
    simp only [Config.toProc, receiveSource, persistentBothTarget, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, parList, InCell.toProc, OutCell.toProc, hin, hout,
      ↓reduceIte]
    rw [hchan]
    refine ⟨
      .par (.input output.chan input.binder input.body)
        (.outPersistent output.chan output.msg),
      .par (.outPersistent output.chan output.msg)
        (.par (.input output.chan input.binder input.body)
          (substProc input.binder (.quote output.msg) input.body)),
      ?_, Step.comm_persistent_out, ?_⟩
    · exact StructEq.par_congr StructEq.refl StructEq.par_zero_right
    · exact StructEq.trans StructEq.par_comm
        (StructEq.trans StructEq.par_assoc
          (StructEq.trans
            (StructEq.par_congr StructEq.refl StructEq.par_comm)
            (StructEq.par_congr StructEq.refl
              (StructEq.par_congr StructEq.refl (StructEq.symm StructEq.par_zero_right)))))

/-- The K ordinary receive branch reifies to rho one-shot COMM. -/
theorem ordinaryReceive_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hin : input.persistent = false)
    (hout : output.persistent = false) :
    StepModStruct (receiveSource input output).toProc (receiveOnceTarget input output).toProc :=
  step_to_rho (Step.ordinaryReceive hchan hin hout)

/-- The K persistent-output branch reifies to rho COMM that keeps the output. -/
theorem persistentOutput_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hin : input.persistent = false)
    (hout : output.persistent = true) :
    StepModStruct (receiveSource input output).toProc (persistentOutputTarget input output).toProc :=
  step_to_rho (Step.persistentOutput hchan hin hout)

/-- The K persistent-input branch reifies to rho COMM that keeps the input. -/
theorem persistentReceive_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hin : input.persistent = true)
    (hout : output.persistent = false) :
    StepModStruct (receiveSource input output).toProc (receiveTarget input output).toProc :=
  step_to_rho (Step.persistentReceive hchan hin hout)

/-- The K persistent-output and persistent-input branch reifies to rho COMM that keeps both cells. -/
theorem persistentBoth_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hin : input.persistent = true)
    (hout : output.persistent = true) :
    StepModStruct (receiveSource input output).toProc (persistentBothTarget input output).toProc :=
  step_to_rho (Step.persistentBoth hchan hin hout)

/-- The K-machine fragment as a labelled transition system. -/
def lts : Denotational.LTS Config Unit where
  step cfg _ cfg' := Step cfg cfg'

end KMachine
end Rho
end MeTTaIL
