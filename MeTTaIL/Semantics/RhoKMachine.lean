/-
Module: MeTTaIL.Semantics.RhoKMachine
Layer: Semantics
Purpose: A K-shaped operational layer for the rho target. The local `f1r3node` K semantics stores
  sends and receives in `<Out>` and `<In>` cells, records candidate IDs in `<InData>` and `<OutData>`,
  checks a match, consumes ordinary receives, keeps persistent sends and receives installed, and then
  spawns the substituted body. This file records the candidate-ID gate and the ordinary and persistent
  one-channel send/receive steps, then proves that those steps reify to the rho COMM relation modulo
  structural congruence.
Imports: MeTTaIL.Semantics.Rho
Trusted boundary: none
Main exports: Rho.KMachine.InCell, Rho.KMachine.OutCell, Rho.KMachine.Config,
  Rho.KMachine.CreationStep, Rho.KMachine.CandidatePair, Rho.KMachine.Step,
  Rho.KMachine.creation_to_struct, Rho.KMachine.step_to_rho,
  Rho.KMachine.ordinaryReceive_to_rho, Rho.KMachine.persistentOutput_to_rho,
  Rho.KMachine.persistentReceive_to_rho, Rho.KMachine.persistentBoth_to_rho
Open obligations: add full multi-cell ID maintenance, arity and pattern matching, and the full
  correspondence with the K configuration rules.
-/
import MeTTaIL.Semantics.Rho

namespace MeTTaIL
namespace Rho
namespace KMachine

abbrev CellId := Nat

/-- A K-style receive cell. `persistent = false` is ordinary `<-`; `persistent = true` is `<=`. -/
structure InCell where
  id : CellId
  chan : Name
  binder : String
  body : Proc
  persistent : Bool
  candidates : List CellId

/-- A K-style output cell. `persistent = false` is ordinary `!`; `persistent = true` is `!!`. -/
structure OutCell where
  id : CellId
  chan : Name
  msg : Proc
  persistent : Bool
  candidates : List CellId

/-- A small K-shaped configuration. The global ID lists mirror the K `<GlobalSetofInIds>` and
    `<GlobalSetofOutIds>` cells for the one-pair fragment. -/
structure Config where
  inputs : List InCell
  outputs : List OutCell
  threads : List Proc
  globalInIds : List CellId
  globalOutIds : List CellId

/-- K offers a pair when either side recorded the other side's ID as a possible match. -/
def CandidatePair (input : InCell) (output : OutCell) : Prop :=
  input.id ∈ output.candidates ∨ output.id ∈ input.candidates

/-- Replace the candidate set recorded in an input cell. -/
def InCell.withCandidates (cell : InCell) (candidates : List CellId) : InCell :=
  { cell with candidates := candidates }

/-- Replace the candidate set recorded in an output cell. -/
def OutCell.withCandidates (cell : OutCell) (candidates : List CellId) : OutCell :=
  { cell with candidates := candidates }

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

/-- Before K creates an `<In>` cell, the surface receive sits in the thread list. -/
def createInputSource (input : InCell) (globalInIds globalOutIds : List CellId) : Config where
  inputs := []
  outputs := []
  threads := [input.toProc]
  globalInIds := globalInIds
  globalOutIds := globalOutIds

/-- Creating an `<In>` cell records all current output IDs as possible candidates. -/
def createInputTarget (input : InCell) (globalInIds globalOutIds : List CellId) : Config where
  inputs := [input.withCandidates globalOutIds]
  outputs := []
  threads := []
  globalInIds := input.id :: globalInIds
  globalOutIds := globalOutIds

/-- Before K creates an `<Out>` cell, the surface send sits in the thread list. -/
def createOutputSource (output : OutCell) (globalInIds globalOutIds : List CellId) : Config where
  inputs := []
  outputs := []
  threads := [output.toProc]
  globalInIds := globalInIds
  globalOutIds := globalOutIds

/-- Creating an `<Out>` cell records all current input IDs as possible candidates. -/
def createOutputTarget (output : OutCell) (globalInIds globalOutIds : List CellId) : Config where
  inputs := []
  outputs := [output.withCandidates globalInIds]
  threads := []
  globalInIds := globalInIds
  globalOutIds := output.id :: globalOutIds

/-- K creation steps move a surface send or receive into a cell and update ID bookkeeping. -/
inductive CreationStep : Config → Config → Prop where
  | input (input : InCell) (globalInIds globalOutIds : List CellId) :
      CreationStep (createInputSource input globalInIds globalOutIds)
        (createInputTarget input globalInIds globalOutIds)
  | output (output : OutCell) (globalInIds globalOutIds : List CellId) :
      CreationStep (createOutputSource output globalInIds globalOutIds)
        (createOutputTarget output globalInIds globalOutIds)

/-- Cell creation is administrative: it preserves the rho process obtained from the configuration. -/
theorem creation_to_struct {cfg cfg' : Config} (hstep : CreationStep cfg cfg') :
    StructEq cfg.toProc cfg'.toProc := by
  cases hstep <;>
    simp [Config.toProc, createInputSource, createInputTarget, createOutputSource,
      createOutputTarget, InCell.withCandidates, OutCell.withCandidates, InCell.toProc,
      OutCell.toProc, parList] <;>
    exact StructEq.refl

/-- The one-cell source configuration for persistent receive firing. -/
def receiveSource (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := [output]
  threads := []
  globalInIds := [input.id]
  globalOutIds := [output.id]

/-- The one-cell target configuration after an ordinary receive consumed the input and output. -/
def receiveOnceTarget (input : InCell) (output : OutCell) : Config where
  inputs := []
  outputs := []
  threads := [substProc input.binder (.quote output.msg) input.body]
  globalInIds := []
  globalOutIds := []

/-- The one-cell target configuration after a persistent output fired and stayed installed. -/
def persistentOutputTarget (input : InCell) (output : OutCell) : Config where
  inputs := []
  outputs := [output]
  threads := [substProc input.binder (.quote output.msg) input.body]
  globalInIds := []
  globalOutIds := [output.id]

/-- The one-cell target configuration after the output was consumed and the input stayed installed. -/
def receiveTarget (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := []
  threads := [substProc input.binder (.quote output.msg) input.body]
  globalInIds := [input.id]
  globalOutIds := []

/-- The one-cell target configuration after persistent input and output both stayed installed. -/
def persistentBothTarget (input : InCell) (output : OutCell) : Config where
  inputs := [input]
  outputs := [output]
  threads := [substProc input.binder (.quote output.msg) input.body]
  globalInIds := [input.id]
  globalOutIds := [output.id]

/-- K-machine receive steps currently checked against rho. -/
inductive Step : Config → Config → Prop where
  | ordinaryReceive {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hcand : CandidatePair input output)
      (hin : input.persistent = false)
      (hout : output.persistent = false) :
      Step (receiveSource input output) (receiveOnceTarget input output)
  | persistentOutput {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hcand : CandidatePair input output)
      (hin : input.persistent = false)
      (hout : output.persistent = true) :
      Step (receiveSource input output) (persistentOutputTarget input output)
  | persistentReceive {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hcand : CandidatePair input output)
      (hin : input.persistent = true)
      (hout : output.persistent = false) :
      Step (receiveSource input output) (receiveTarget input output)
  | persistentBoth {input : InCell} {output : OutCell}
      (hchan : input.chan = output.chan)
      (hcand : CandidatePair input output)
      (hin : input.persistent = true)
      (hout : output.persistent = true) :
      Step (receiveSource input output) (persistentBothTarget input output)

/-- K-shaped receive steps reify to rho COMM modulo `|` structure. -/
theorem step_to_rho {cfg cfg' : Config} (hstep : Step cfg cfg') :
    StepModStruct cfg.toProc cfg'.toProc := by
  cases hstep
  · rename_i input output hchan hcand hin hout
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
  · rename_i input output hchan hcand hin hout
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
  · rename_i input output hchan hcand hin hout
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
  · rename_i input output hchan hcand hin hout
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
    (hchan : input.chan = output.chan) (hcand : CandidatePair input output)
    (hin : input.persistent = false) (hout : output.persistent = false) :
    StepModStruct (receiveSource input output).toProc (receiveOnceTarget input output).toProc :=
  step_to_rho (Step.ordinaryReceive hchan hcand hin hout)

/-- The K persistent-output branch reifies to rho COMM that keeps the output. -/
theorem persistentOutput_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hcand : CandidatePair input output)
    (hin : input.persistent = false) (hout : output.persistent = true) :
    StepModStruct (receiveSource input output).toProc (persistentOutputTarget input output).toProc :=
  step_to_rho (Step.persistentOutput hchan hcand hin hout)

/-- The K persistent-input branch reifies to rho COMM that keeps the input. -/
theorem persistentReceive_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hcand : CandidatePair input output)
    (hin : input.persistent = true) (hout : output.persistent = false) :
    StepModStruct (receiveSource input output).toProc (receiveTarget input output).toProc :=
  step_to_rho (Step.persistentReceive hchan hcand hin hout)

/-- The K persistent-output and persistent-input branch reifies to rho COMM that keeps both cells. -/
theorem persistentBoth_to_rho (input : InCell) (output : OutCell)
    (hchan : input.chan = output.chan) (hcand : CandidatePair input output)
    (hin : input.persistent = true) (hout : output.persistent = true) :
    StepModStruct (receiveSource input output).toProc (persistentBothTarget input output).toProc :=
  step_to_rho (Step.persistentBoth hchan hcand hin hout)

/-- The K-machine fragment as a labelled transition system. -/
def lts : Denotational.LTS Config Unit where
  step cfg _ cfg' := Step cfg cfg'

end KMachine
end Rho
end MeTTaIL
