/-
Module: MeTTaIL.Semantics.RhoCompiler
Layer: Semantics
Purpose: A checked packet-level bridge from the existing MeTTaIL base matcher to the rho target.
  The bridge follows the direct-rule shape in `mettail-rust/gslt2rho`: a matched rewrite sends the
  contractum to a persistent listener, and the listener emits the encoded contractum at the source
  term location.
Imports: MeTTaIL.Semantics.Rho
Trusted boundary: none
Main exports: Rho.Compiler.ruleChannel, Rho.Compiler.contractumBinder,
  Rho.Compiler.contractumForwarder, Rho.Compiler.contractumPacket, Rho.Compiler.contractumRun,
  Rho.Compiler.contractumEmitted, Rho.Compiler.contractumForwarder_emits,
  Rho.Compiler.applyBaseRewrite_reduces_and_emits
Open obligations: replace the contractum packet with the full matcher/router process, add contextual
  and set-automaton channels, prove freshness for compiler-generated binders, and then prove the
  two-direction MeTTaIL-to-rho simulation.
-/
import MeTTaIL.Semantics.Rho

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

end Compiler
end Rho
end MeTTaIL
