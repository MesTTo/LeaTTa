-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Types
import MettaHyperonFull.Operational.Semantics

namespace Metta

/-- Well-formed atom relative to a type environment. This is deliberately permissive: MeTTa is
    gradually typed and `%Undefined%` is a legal type. -/
inductive WFAtom (env : TypeEnv) : Atom → Prop where
  | sym (s : String) : WFAtom env (Atom.sym s)
  | var (x : VarName) : WFAtom env (Atom.var x)
  | ground (g : Ground) : WFAtom env (Atom.gnd g)
  | expr (xs : List Atom) : (∀ a, a ∈ xs → WFAtom env a) → WFAtom env (Atom.expr xs)

inductive WFSpace (env : TypeEnv) : Space → Prop where
  | mk (s : Space) : (∀ a, a ∈ s.atoms → WFAtom env a) → WFSpace env s

/-- A state is well-formed when each of its four register spaces is well-formed. -/
inductive WFState (env : TypeEnv) : State → Prop where
  | mk (s : State) :
      WFSpace env s.input → WFSpace env s.kb → WFSpace env s.work → WFSpace env s.output →
      WFState env s

/-- Every atom is syntactically well-formed. Well-formedness here is purely structural
    (MeTTa is gradually typed and `%Undefined%` is a legal type), so the predicate always
    holds; meaningful type discipline lives in `HasType` and `TypeEnv`. -/
theorem wfAtom_all (env : TypeEnv) : (a : Atom) → WFAtom env a
  | .sym s => .sym s
  | .var x => .var x
  | .gnd g => .ground g
  | .expr xs => .expr xs fun a _ => wfAtom_all env a

/-- Every atom produced by ordinary substitution remains syntactically well-formed. -/
theorem subst_preserves_wf (env : TypeEnv) (σ : Subst) (a : Atom) :
    WFAtom env a → WFAtom env (Subst.apply σ a) :=
  fun _ => wfAtom_all env (Subst.apply σ a)

/-- Every space is well-formed, since every atom is. -/
theorem wfSpace_all (env : TypeEnv) (s : Space) : WFSpace env s :=
  .mk s (fun a _ => wfAtom_all env a)

/-- Every reachable runtime state is well-formed: the four-register machine never builds a
    malformed state. -/
theorem wfState_all (env : TypeEnv) (s : State) : WFState env s :=
  .mk s (wfSpace_all env _) (wfSpace_all env _) (wfSpace_all env _) (wfSpace_all env _)

end Metta
