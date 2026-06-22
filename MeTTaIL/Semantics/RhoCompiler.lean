/-
Module: MeTTaIL.Semantics.RhoCompiler
Layer: Semantics
Purpose: A checked packet-level bridge from the existing MeTTaIL base matcher to the rho target.
  The bridge follows the direct-rule shape in `mettail-rust/gslt2rho`: a matched rewrite sends the
  contractum to a persistent listener, and the listener emits the encoded contractum at the source
  term location.
Imports: MeTTaIL.Semantics.RhoKMachine
Trusted boundary: none
Main exports: Rho.Compiler.ruleChannel, Rho.Compiler.contractumBinder,
  Rho.Compiler.contractumForwarder, Rho.Compiler.contractumPacket, Rho.Compiler.contractumRun,
  Rho.Compiler.contractumEmitted, Rho.Compiler.contractumForwarder_emits,
  Rho.Compiler.contractumInputCell, Rho.Compiler.contractumOutputCell,
  Rho.Compiler.contractum_kstep, Rho.Compiler.contractumRun_struct_kSource,
  Rho.Compiler.contractumRun_kstep_to_rho, Rho.Compiler.contractum_kstep_to_rho,
  Rho.Compiler.applyBaseRewrite_reduces_emits_and_reifies_kstep,
  Rho.Compiler.applyBaseRewrite_reduces_and_emits
Open obligations: replace the contractum packet with the full matcher/router process, add contextual
  and set-automaton channels, prove freshness for compiler-generated binders, and then prove the
  two-direction MeTTaIL-to-rho simulation.
-/
import MeTTaIL.Semantics.RhoKMachine

namespace MeTTaIL
namespace Rho
namespace Compiler

/-- Dedicated channel used by the packet-level bridge for one rewrite declaration. -/
def ruleChannel (rd : RewriteDecl) : Name :=
  .var ("rule:" ++ rd.name)

/-- Binder name reserved for the contractum packet of one rewrite declaration. -/
def contractumBinder (rd : RewriteDecl) : String :=
  "__contractum:" ++ rd.name

/-- Persistent listener that forwards a matched contractum to the source term location. -/
def contractumForwarder (rd : RewriteDecl) (source : AST) : Proc :=
  payloadForwarder (ruleChannel rd) (termLocation source) (contractumBinder rd)

/-- Packet sent by the matcher/router once a base rewrite has produced a contractum. -/
def contractumPacket (rd : RewriteDecl) (contractum : AST) : Proc :=
  .out (ruleChannel rd) (encodeAST contractum)

/-- The initial rho process for the packet-level direct-rule bridge. -/
def contractumRun (rd : RewriteDecl) (source contractum : AST) : Proc :=
  .par (contractumForwarder rd source) (contractumPacket rd contractum)

/-- The rho process after the packet has been received and the encoded contractum has been emitted. -/
def contractumEmitted (rd : RewriteDecl) (source contractum : AST) : Proc :=
  .par (contractumForwarder rd source)
    (.out (substName (contractumBinder rd) (.quote (encodeAST contractum)) (termLocation source))
      (encodeAST contractum))

/-- K receive cell installed for the packet-level direct-rule bridge. Candidate `1` is the packet. -/
def contractumInputCell (rd : RewriteDecl) (source : AST) : KMachine.InCell where
  id := 0
  chan := ruleChannel rd
  binder := contractumBinder rd
  body := .out (termLocation source) (.drop (.var (contractumBinder rd)))
  persistent := true
  candidates := [1]
  matchReady := KMachine.acceptAny

/-- K output cell carrying the matched contractum packet. Candidate `0` is the listener. -/
def contractumOutputCell (rd : RewriteDecl) (contractum : AST) : KMachine.OutCell where
  id := 1
  chan := ruleChannel rd
  msg := encodeAST contractum
  persistent := false
  candidates := [0]

/-- The packet-level direct-rule bridge is a K-machine persistent-receive step. -/
theorem contractum_kstep (rd : RewriteDecl) (source contractum : AST) :
    KMachine.Step
      (KMachine.receiveSource (contractumInputCell rd source) (contractumOutputCell rd contractum))
      (KMachine.receiveTarget (contractumInputCell rd source) (contractumOutputCell rd contractum)) := by
  exact KMachine.Step.persistentReceive rfl
    (KMachine.readyPair_of_input_records_output
      (by simp [contractumInputCell, contractumOutputCell])
      (by simp [KMachine.MatchedOne, KMachine.acceptAny, contractumInputCell, contractumOutputCell]))
    rfl rfl

/-- The packet/listener rho process is the reification of the corresponding created K cells, up to
    the trailing parallel unit introduced by `parList`. -/
theorem contractumRun_struct_kSource (rd : RewriteDecl) (source contractum : AST) :
    StructEq (contractumRun rd source contractum)
      (KMachine.receiveSource (contractumInputCell rd source) (contractumOutputCell rd contractum)).toProc := by
  simp [contractumRun, contractumForwarder, contractumPacket, contractumInputCell,
    contractumOutputCell, KMachine.receiveSource, KMachine.Config.toProc, KMachine.InCell.toProc,
    KMachine.OutCell.toProc, payloadForwarder, parList]
  exact StructEq.par_congr StructEq.refl (StructEq.symm StructEq.par_zero_right)

/-- The compiler K-step reifies to rho reduction modulo parallel-structure laws. -/
theorem contractum_kstep_to_rho (rd : RewriteDecl) (source contractum : AST) :
    StepModStruct
      (KMachine.receiveSource (contractumInputCell rd source) (contractumOutputCell rd contractum)).toProc
      (KMachine.receiveTarget (contractumInputCell rd source) (contractumOutputCell rd contractum)).toProc := by
  exact KMachine.step_to_rho (contractum_kstep rd source contractum)

/-- The actual packet/listener rho process takes the K-machine communication step modulo `|` laws. -/
theorem contractumRun_kstep_to_rho (rd : RewriteDecl) (source contractum : AST) :
    StepModStruct (contractumRun rd source contractum)
      (KMachine.receiveTarget (contractumInputCell rd source) (contractumOutputCell rd contractum)).toProc := by
  rcases contractum_kstep_to_rho rd source contractum with ⟨u, v, hsrc, hstep, htgt⟩
  exact ⟨u, v, StructEq.trans (contractumRun_struct_kSource rd source contractum) hsrc, hstep, htgt⟩

/-- The packet-level direct-rule listener emits the encoded contractum. -/
theorem contractumForwarder_emits (rd : RewriteDecl) (source contractum : AST) :
    Relation.ReflTransGen Step (contractumRun rd source contractum)
      (contractumEmitted rd source contractum) := by
  simpa [contractumRun, contractumEmitted, contractumForwarder, contractumPacket,
    ruleChannel, contractumBinder] using
    payloadForwarder_emits (ruleChannel rd) (termLocation source) (contractumBinder rd)
      (encodeAST contractum)

/-- A successful base matcher result is a MeTTaIL reduction and can be emitted by the rho bridge. -/
theorem applyBaseRewrite_reduces_and_emits (p : Presentation) (rd : RewriteDecl)
    (source contractum : AST) (hmem : rd ∈ p.rewrites)
    (h : applyBaseRewrite rd source = some contractum) :
    Reduces p source contractum ∧
      Relation.ReflTransGen Step (contractumRun rd source contractum)
      (contractumEmitted rd source contractum) := by
  exact ⟨reduces_of_applyBaseRewrite p rd source contractum hmem h,
    contractumForwarder_emits rd source contractum⟩

/-- A successful base matcher result is also the corresponding ready K-machine packet step. -/
theorem applyBaseRewrite_reduces_emits_and_reifies_kstep (p : Presentation) (rd : RewriteDecl)
    (source contractum : AST) (hmem : rd ∈ p.rewrites)
    (h : applyBaseRewrite rd source = some contractum) :
    Reduces p source contractum ∧
      StepModStruct (contractumRun rd source contractum)
        (KMachine.receiveTarget (contractumInputCell rd source) (contractumOutputCell rd contractum)).toProc ∧
      Relation.ReflTransGen Step (contractumRun rd source contractum)
        (contractumEmitted rd source contractum) := by
  exact ⟨reduces_of_applyBaseRewrite p rd source contractum hmem h,
    contractumRun_kstep_to_rho rd source contractum,
    contractumForwarder_emits rd source contractum⟩

end Compiler
end Rho
end MeTTaIL
