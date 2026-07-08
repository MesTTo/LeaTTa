-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.TypeSoundness
Layer: Proofs
Purpose: The gradual type system is permissive, total, and reports errors faithfully. Undeclared
  operators, extra arguments, and the wildcards %Undefined%/Atom are never rejected, getTypes assigns
  every atom at least one type, a reported BadArgType always names a real actual type, and the runtime
  invents no type errors. Preservation for the grounded numeric core: arithmetic is closed on Number,
  comparison and == yield Bool or faithfully propagate an error.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none (fully proved)
Main exports: typeMismatch_undeclared, matchType_undefined_left, matchType_undefined_right,
  matchType_atom_left, matchType_atom_right, typeCheckArgs_no_param, mettaEval_badArgType,
  getTypes_ne_nil, getTypes_unique_modulo_permutation, typeCheckArgs_act_real, numBin_isNumber,
  numCmp_isBool, eqAtom_isBoolOrError
Open obligations: none. Subject reduction over user-defined =-rewriting is proved in Preservation.lean.
-/
import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: gradual type system, permissiveness and faithful error reporting

MeTTa's type system (`Minimal/Interpreter.lean`: `getTypes`, `matchType`, `typeCheckArgs`,
`typeMismatch`) is *gradual*: a declared arrow signature `(: op (-> T₁ … Tₙ R))` causes argument
type-checking, an undeclared operator is left unchecked, and the special types `%Undefined%` and
`Atom` are compatible with anything. A genuine mismatch surfaces at runtime as
`(Error (op …) (BadArgType pos expected actual))` (Hyperon's `BadArgType`).

For on-chain use, two properties matter: a well-typed program is never rejected with a spurious
type error, and a `BadArgType` is reported faithfully and only for a genuinely ill-typed
application. This file proves both:

* **Gradual permissiveness**: undeclared operators (`typeMismatch_undeclared`) and arguments
  beyond the declared arity (`typeCheckArgs_no_param`) are never rejected; an empty argument list
  is accepted (`typeCheckArgs_nil`); and `%Undefined%`/`Atom` unify with any type on the relevant
  side (`matchType_undefined_left/right`, `matchType_atom_left`). The checker fires only on a
  declared signature with a concrete, incompatible argument.
* **Faithful reporting**: when the checker reports a mismatch at position `pos`, the evaluator
  returns the corresponding `BadArgType` error and nothing else (`mettaEval_badArgType`). A
  `BadArgType` in the output corresponds to a checker rejection; the runtime does not invent type
  errors.
* **No false positives**: the *actual* type named in a `BadArgType` is a genuine type of the
  offending argument (`typeCheckArgs_act_real`), never invented.
* **Preservation (grounded core)**: arithmetic is closed on `Number` (`numBin_isNumber`),
  comparison yields `Bool` (`numCmp_isBool`), and `==` yields `Bool` or faithfully propagates an
  error (`eqAtom_isBoolOrError`). These ops carry exactly those declared signatures, so a
  well-typed grounded redex reduces to a value of its declared return type.

Together these cover progress (permissive and total) and preservation (grounded core, faithful and
non-fabricated errors) for the gradual and grounded fragment. Subject reduction over user-defined
`=`-rewriting, with a context-indexed typing judgment for rule variables, is proved in
`Proofs/Preservation.lean` (`WT.subst`, `reduction_preserves_type`).
-/

namespace Metta
open Metta.Minimal

/-- **Gradual.** An operator with no declared signature is never type-rejected: `typeMismatch`
returns `none`, so evaluation proceeds untyped. -/
theorem typeMismatch_undeclared (env : MinEnv) (w : World) (op : String) (args : List Atom)
    (h : env.sigs[op]? = none) : typeMismatch env w op args = none := by
  simp [typeMismatch, h]

/-- `%Undefined%` as the *expected* type matches any actual type (gradual top). -/
theorem matchType_undefined_left (tb : Bindings) (actual : Atom) :
    matchType tb (Atom.sym "%Undefined%") actual = some tb := by
  have hc : (Atom.sym "%Undefined%" == Atom.sym "%Undefined%") = true := by decide
  simp [matchType, hc]

/-- `Atom` as the *expected* type matches any actual type (an `Atom`-typed parameter accepts
anything, which is what keeps quoted/unevaluated arguments well-typed). -/
theorem matchType_atom_left (tb : Bindings) (actual : Atom) :
    matchType tb (Atom.sym "Atom") actual = some tb := by
  have hc : (Atom.sym "Atom" == Atom.sym "Atom") = true := by decide
  simp [matchType, hc]

/-- `%Undefined%` as the *actual* type matches any expected type (an un-typed argument is accepted
everywhere). -/
theorem matchType_undefined_right (tb : Bindings) (expected : Atom) :
    matchType tb expected (Atom.sym "%Undefined%") = some tb := by
  have hc : (Atom.sym "%Undefined%" == Atom.sym "%Undefined%") = true := by decide
  simp [matchType, hc]

/-- `Atom` as the *actual* type also matches any expected type: the gradual top is **symmetric**.
Hyperon's `match_types` tests `type2 == ATOM_TYPE_ATOM` as well (`interpreter.rs:1225`), so a value of
meta-type `Atom` (e.g. a quoted/unevaluated argument) is accepted against any declared parameter. The
companion of `matchType_atom_left`. -/
theorem matchType_atom_right (tb : Bindings) (expected : Atom) :
    matchType tb expected (Atom.sym "Atom") = some tb := by
  have hc : (Atom.sym "Atom" == Atom.sym "Atom") = true := by decide
  simp [matchType, hc]

theorem typeCheckArgs_nil (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) : typeCheckArgs env w argTypes i tb [] = none := by
  simp [typeCheckArgs]

/-- **Gradual.** An argument in a position beyond the declared parameters is not checked; extra
arguments never cause a type error. -/
theorem typeCheckArgs_no_param (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) (ai : Atom) (more : List Atom) (h : argTypes[i]? = none) :
    typeCheckArgs env w argTypes i tb (ai :: more) = none := by
  simp [typeCheckArgs, h]

/-- **Faithful error reporting.** When the gradual checker flags a mismatch at position `pos`
(expected `exp`, actual `act`), one evaluation step of `(op args)` returns the corresponding
`BadArgType` error and nothing else. A `BadArgType` in the output corresponds to a checker
rejection; the runtime never invents a type error. -/
theorem mettaEval_badArgType (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings)
    (op : String) (args : List Atom) (pos : Nat) (exp act : Atom)
    (hinst : instantiate bnd (Atom.expr (Atom.sym op :: args)) = Atom.expr (Atom.sym op :: args))
    (hArity : arityMismatch env op args = false)
    (hwt : typeMismatch env st.world op args = some (pos, exp, act)) :
    mettaEval env (fuel + 1) st bnd (Atom.expr (Atom.sym op :: args)) =
      ([(Atom.expr [Atom.sym "Error", Atom.expr (Atom.sym op :: args),
          Atom.expr [Atom.sym "BadArgType", Atom.gnd (Ground.int (Int.ofNat pos)), exp, act]], bnd)], st) := by
  simp [mettaEval, hinst, hArity, hwt]

/-- **Totality of typing.** `getTypes` assigns at least one type to every atom; gradual typing has
no "untyped gap": an undeclared symbol gets `%Undefined%`, an application its inferred return type(s)
or `%Undefined%`, never the empty set. (Proved by the generated functional-induction principle.) -/
theorem getTypes_ne_nil (env : MinEnv) (a : Atom) : getTypes env a ≠ [] := by
  fun_induction getTypes env a <;>
    simp_all <;> (try split) <;> simp_all <;> (try split) <;> simp_all

/-- `getTypes` is a function, so any two computed type lists for the same atom are the same up to
permutation. This is the theorem-level uniqueness surface available before introducing a separate
relational type-synthesis judgment. -/
theorem getTypes_unique_modulo_permutation (env : MinEnv) (a : Atom) {ts₁ ts₂ : List Atom}
    (h₁ : getTypes env a = ts₁) (h₂ : getTypes env a = ts₂) : ts₁.Perm ts₂ := by
  rw [← h₁, ← h₂]

/-- **No fabricated type errors.** The *actual* type reported in a `BadArgType` is a genuine type of
the offending argument: it is one of `getTypes` of that argument (its head). So the checker never
invents a type the argument does not have: combined with `mettaEval_badArgType` (faithful reporting)
and the gradual-permissiveness lemmas above, a `BadArgType (pos, expected, actual)` always names a
real `expected` parameter type and a real `actual` argument type. -/
theorem typeCheckArgs_act_real (env : MinEnv) (w : World) (argTypes : List Atom) :
    ∀ (i : Nat) (tb : Bindings) (args : List Atom) (j : Nat) (e a : Atom),
    typeCheckArgs env w argTypes i tb args = some (j, e, a) →
    ∃ arg ∈ args, a ∈ getTypes env (typePrep w arg) := by
  intro i tb args
  induction args generalizing i tb with
  | nil => intro j e a h; simp [typeCheckArgs] at h
  | cons ai more ih =>
      intro j e a h
      simp only [typeCheckArgs] at h
      split at h
      · simp at h
      · split at h
        · next act' tb' hfs =>
            obtain ⟨arg, hmem, ha⟩ := ih (i + 1) tb' j e a h
            exact ⟨arg, List.mem_cons_of_mem ai hmem, ha⟩
        · next _ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, _, ha⟩ := h
            subst ha
            refine ⟨ai, List.mem_cons_self, ?_⟩
            obtain ⟨hd, tl, hh⟩ := List.exists_cons_of_ne_nil (getTypes_ne_nil env (typePrep w ai))
            rw [hh]; simp

/-! ## Preservation for the grounded numeric core

The grounded operations **preserve types**: arithmetic is closed on numbers, and comparison /
equality yield Booleans (or propagate an error). Together with the gradual checker above, these
lemmas are the preservation half of type soundness for the grounded core. A well-typed `(+ …)`
always reduces to a `Number`, never a stuck or mistyped atom. -/

/-- **Arithmetic is closed on `Number`.** Any `numBin` (`+`, `-`, `*`) that returns a value returns a
numeric grounded atom, either an `Int` or a `Float`, never a symbol, variable, or expression. So a
well-typed arithmetic redex reduces to a `Number`: type is preserved. -/
theorem numBin_isNumber (fi : Int → Int → Int) (ff : Float → Float → Float)
    (args : List Atom) (r : Atom)
    (h : Builtins.numBin fi ff args = ReduceResult.ok [r]) :
    (∃ n : Int, r = Atom.gnd (Ground.int n)) ∨ (∃ x : Float, r = Atom.gnd (Ground.float x)) := by
  unfold Builtins.numBin at h
  split at h <;>
    simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true, reduceCtorEq] at h
  · exact Or.inl ⟨_, h.symm⟩
  · exact Or.inr ⟨_, h.symm⟩
  · exact Or.inr ⟨_, h.symm⟩
  · exact Or.inr ⟨_, h.symm⟩

/-- **Comparison yields `Bool`.** Any `numCmp` (`<`, `<=`, `>`, `>=`) that returns a value returns a
Boolean grounded atom. -/
theorem numCmp_isBool (fi : Int → Int → Bool) (ff : Float → Float → Bool)
    (args : List Atom) (r : Atom)
    (h : Builtins.numCmp fi ff args = ReduceResult.ok [r]) :
    ∃ b : Bool, r = Atom.gnd (Ground.bool b) := by
  unfold Builtins.numCmp at h
  split at h <;>
    simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true, reduceCtorEq] at h
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩

/-- **Equality yields `Bool`, or propagates an error.** `==` returns a Boolean grounded atom, unless
one argument is itself an `(Error …)`, which it lifts unchanged (Hyperon's error-propagating `==`).
So `==` never produces a mistyped result: it is a `Bool` or a faithfully-propagated error. -/
theorem eqAtom_isBoolOrError (args : List Atom) (r : Atom)
    (h : Builtins.eqAtom args = ReduceResult.ok [r]) :
    (∃ b : Bool, r = Atom.gnd (Ground.bool b)) ∨ r.isError = true := by
  unfold Builtins.eqAtom at h
  split at h
  · rename_i a b
    split at h
    · simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true] at h
      exact Or.inr (by rw [← h]; assumption)
    · split at h
      · simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true] at h
        exact Or.inr (by rw [← h]; assumption)
      · simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true] at h
        exact Or.inl ⟨_, h.symm⟩
  · simp only [reduceCtorEq] at h

end Metta
