; SPDX-FileCopyrightText: 2026 MesTTo
; SPDX-License-Identifier: Apache-2.0

; Regression for ported type/error stdlib helpers (Hyperon stdlib.metta).
!(assertEqual (noreduce-eq a a) True)
!(assertEqual (noreduce-eq a b) False)
!(assertEqual (if-error (Error x y) yes no) yes)
!(assertEqual (if-error 42 yes no) no)
!(assertEqual (return-on-error 42 ok) ok)
!(assertEqual (is-function (-> A B)) True)
!(assertEqual (is-function Number) False)
!(assertEqual (match-types Number Number yes no) yes)
!(assertEqual (match-types Number String yes no) no)
!(assertEqual (match-types Atom String yes no) yes)
!(assertEqual (match-types Number %Undefined% yes no) yes)
!(assertEqual (first-from-pair (aa bb)) aa)
!(assertEqual (for-each-in-atom () nop) ())
!(assertEqual (for-each-in-atom (1 2 3) nop) ())
!(assertEqual (get-type 5) Number)
!(assertEqual (get-type-space &self 5) Number)
; Repair #25: `Type` and `ErrorType` are ordinary symbol atoms at the
; syntactic meta-type boundary. Their declarations live in the type
; environment and do not change `get-metatype`.
!(assertEqual (get-metatype Type) Symbol)
!(assertEqual (get-metatype ErrorType) Symbol)
!(assertEqual (get-type 5 &self)
  (Error (get-type 5 &self) IncorrectNumberOfArguments))
!(assertEqual (type-cast 5 Number &self) 5)
!(assertEqual (type-cast 5 String &self) (Error 5 BadType))
!(assertEqual (type-cast foo Symbol &self) foo)

; Application type inference must not swallow a failed argument match.
(: r1-bad-g (-> A R))
(: r1-bad-b B)
!(assertEqualToResult (get-type-space &self (r1-bad-g r1-bad-b)) ())
!(assertEqual (r1-bad-g r1-bad-b)
  (Error (r1-bad-g r1-bad-b) (BadArgType 1 A B)))

; Independent annotation variables with the same source spelling must not
; capture one another during nested application inference.
(: r7-g (-> $t A R))
(: r7-b B)
(: r7-k (-> $t))
!(assertEqual (get-type-space &self (r7-g r7-b (r7-k))) R)

; The embedded metta boundary must consume its expected type.  Before repair
; #8 it ignored B and returned r8-a unchanged.
(: r8-a A)
!(assertEqual (metta r8-a B &self)
  (Error r8-a (BadType B A)))

; Multiple function signatures are scanned in source order from the same
; declaration list observed by get-type.  An earlier applicable declaration
; must not be lost to a later one.
(: r10-f (-> A RA))
(: r10-f (-> B RB))
(: r10-a A)
!(assertEqual (r10-f r10-a) (r10-f r10-a))

; An inapplicable first declaration is skipped in favor of a later applicable
; one, while total failure retains every diagnostic in declaration order.
(: r10-g (-> B RB))
(: r10-g (-> A RA))
!(assertEqual (r10-g r10-a) (r10-g r10-a))
(: r10-h (-> A RA))
(: r10-h (-> B RB))
(: r10-c C)
!(assertEqualToResult (r10-h r10-c)
  ((Error (r10-h r10-c) (BadArgType 1 A C))
   (Error (r10-h r10-c) (BadArgType 1 B C))))

; The selected declaration owns both the evaluation mask and return policy.
; The first signature quotes its argument and returns Atom, so neither the
; thunk nor the produced readout is recursively evaluated.
(: r10-owner (-> Atom Atom))
(: r10-owner (-> Number %Undefined%))
(: (r10-thunk) Number)
(= (r10-thunk) 7)
(= (r10-owner $x) (r10-produced $x))
(= (r10-produced $x) (r10-done $x))
!(assertEqualToResult (r10-owner (r10-thunk))
  ((r10-produced (r10-thunk))))

; A non-arrow declaration preserves tuple fallback even when an arrow
; declaration fails.  Because a semantic success exists, the published
; success-priority boundary suppresses the latent diagnostic.
(: r10-tuple PlainType)
(: r10-tuple (-> A R))
!(assertEqualToResult (r10-tuple r10-c)
  ((r10-tuple r10-c)))

; Expected-return selection is conjunctive: an earlier argument-applicable
; signature with the wrong result type must not shadow a later applicable one.
; The selected result is checked against that signature's return type.
(: r11-f (-> X A))
(: r11-f (-> X B))
(: r11-a X)
(: r11-ra A)
(= (r11-f $x) r11-ra)
!(assertEqual (metta (r11-f r11-a) B &self)
  (Error r11-ra (BadType B A)))

; A selected result of the expected type remains accepted.
(: r11-good-f (-> X A))
(: r11-good-f (-> X B))
(: r11-rb B)
(= (r11-good-f $x) r11-rb)
!(assertEqual (metta (r11-good-f r11-a) B &self) r11-rb)

; `Atom` remains a return passthrough even under a more specific outer
; expectation: the selected policy deliberately leaves the expression quoted.
(: r11-atom-f (-> X Atom))
(: r11-atom-f (-> X B))
(: r11-g (-> B))
(: r11-done B)
(= (r11-atom-f $x) (r11-g))
(= (r11-g) r11-done)
!(assertEqualToResult (metta (r11-atom-f r11-a) B &self) ((r11-g)))

; The expected-return-selected signature also owns the argument-evaluation
; policy.  Selecting the later `(-> X B)` signature evaluates the thunk;
; selecting the earlier `(-> Atom A)` signature would quote it.
(: r11-mask (-> Atom A))
(: r11-mask (-> X B))
(: (r11-thunk) X)
(: r11-v X)
(: r11-bad A)
(: r11-good B)
(= (r11-thunk) r11-v)
(= (r11-mask (r11-thunk)) r11-bad)
(= (r11-mask r11-v) r11-good)
!(assertEqual (metta (r11-mask (r11-thunk)) B &self) r11-good)

; A type variable that the argument fold binds to `Atom` is not itself a
; literal return wildcard.  The expected-return gate must inspect the raw
; declared return under the threaded bindings, matching upstream's rejection.
(: r11-dependent-f (-> (P $t) $t))
(: r11-dependent-a (P Atom))
(: r11-dependent-rb B)
(= (r11-dependent-f $x) r11-dependent-rb)
!(assertEqual (metta (r11-dependent-f r11-dependent-a) B &self)
  (Error (r11-dependent-f r11-dependent-a) (BadType B Atom)))

; A type variable that an earlier argument binds to `Atom` is not itself a
; literal argument wildcard at a later position.  The raw formal `$t` must be
; matched under the threaded binding, while `Atom` is used only in the error.
(: r12-f (-> (P $t) $t R))
(: r12-a (P Atom))
(: r12-b B)
(= (r12-f $x $y) r12-ok)
!(assertEqual (r12-f r12-a r12-b)
  (Error (r12-f r12-a r12-b) (BadArgType 2 Atom B)))

; Every failed actual type contributes a diagnostic, even when several types
; belong to the same argument.  Declaration order is retained within the
; argument's error block.
(: r13-many B)
(: r13-many C)
(: r13-all-fail (-> A R))
(= (r13-all-fail $x) r13-ok)
!(assertEqualToResult (r13-all-fail r13-many)
  ((Error (r13-all-fail r13-many) (BadArgType 1 A B))
   (Error (r13-all-fail r13-many) (BadArgType 1 A C))))

; Failed alternatives remain latent when an argument has a successful type.
; If a later argument rejects the candidate, later argument blocks precede
; those earlier latent diagnostics.
(: r13-bad D)
(: r13-mixed (-> B A R))
(= (r13-mixed $x $y) r13-ok)
!(assertEqualToResult (r13-mixed r13-many r13-bad)
  ((Error (r13-mixed r13-many r13-bad) (BadArgType 2 A D))
   (Error (r13-mixed r13-many r13-bad) (BadArgType 1 B C))))

; The block-prepend law extends across every argument, while each block keeps
; its own declaration order.
(: r13-middle A)
(: r13-middle D)
(: r13-last E)
(: r13-three (-> B A C R))
(= (r13-three $x $y $z) r13-ok)
!(assertEqualToResult (r13-three r13-many r13-middle r13-last)
  ((Error (r13-three r13-many r13-middle r13-last) (BadArgType 3 C E))
   (Error (r13-three r13-many r13-middle r13-last) (BadArgType 2 A D))
   (Error (r13-three r13-many r13-middle r13-last) (BadArgType 1 B C))))

; Multiple matching actual types do not duplicate an otherwise non-dependent
; observable.  Applicability commits to the first complete surviving branch.
(: r13-one-result (-> $u R))
(= (r13-one-result $x) r13-ok)
!(assertEqualToResult (r13-one-result r13-many) (r13-ok))

; Repair #14: a later actual-type presentation remains available when an
; earlier presentation fails the dependent return gate.
(: r14-dependent (-> $u $u))
(: r14-c-result C)
(= (r14-dependent $x) r14-c-result)
!(assertEqual (metta (r14-dependent r13-many) C &self) r14-c-result)

; Repair #16 / W12: unconstrained applicability commits to `u := B`.
; The selected return policy then rejects the produced `C`; evaluation does
; not backtrack to the later `u := C` presentation.
!(assertEqual (r14-dependent r13-many)
  (Error r14-c-result (BadType B C)))

; Repair #15: expression applicability owns the complete error protocol.
; A failed alternative is emitted before the return-gate failure; the old
; whole-application pre-cast shadowed the first diagnostic.
(: r15-return-fail (-> B B))
(: r15-b-result B)
(= (r15-return-fail $x) r15-b-result)
!(assertEqualToResult (metta (r15-return-fail r13-many) X &self)
  ((Error (r15-return-fail r13-many) (BadArgType 1 B C))
   (Error (r15-return-fail r13-many) (BadType X B))))

; Two-choice-point DFS canary.  Argument presentations are
; explored lexicographically: (B,D), (B,E), (C,D), (C,E); the expected return
; admits the third branch.  The no-expected companion below observes that the
; first committed branch is (B,D).  Together with the published row-major fold
; these pin first-branch lexicographic order; ground expectations cannot by
; themselves distinguish the two middle branches.
(: r14-left B)
(: r14-left C)
(: r14-right D)
(: r14-right E)
(: r14-two-choice (-> $u $v (Pair $u $v)))
(: r14-two-choice-result (Pair C D))
(= (r14-two-choice $x $y) r14-two-choice-result)
!(assertEqual (metta (r14-two-choice r14-left r14-right)
    (Pair C D) &self)
  r14-two-choice-result)
!(assertEqual (r14-two-choice r14-left r14-right)
  (Error r14-two-choice-result (BadType (Pair B D) (Pair C D))))

; Repair #16 / W14: ordinary argument evaluation is type-directed.  The
; static `%Undefined%` admits the thunk, but its evaluated `C` result is cast
; against the selected formal `B`; the error source is the value itself.
(: r16-h (-> B R))
(: (r16-j) %Undefined%)
(: r16-v C)
(: r16-ok R)
(= (r16-j) r16-v)
(= (r16-h $x) r16-ok)
!(assertEqual (r16-h (r16-j))
  (Error r16-v (BadType B C)))

; Repair #18: a signature-private variable must not capture an equal-spelled
; variable supplied as the application's expected type.  The signature is
; localized at selection consumption, so its argument binds privately while
; the public expected variable independently accepts the result type.
(: r18-a A)
(: r18-f (-> $t B))
(: r18-rb B)
(= (r18-f $x) r18-rb)
!(assertEqual (metta (r18-f r18-a) $t &self) r18-rb)

; Repair #19: the return gate binds the caller-visible expected variable `$t`
; to `B`.  The projected public binding seeds both argument evaluation and
; rule reduction, while private type-freshening names remain hidden.
(: r19-f (-> Atom B))
(= (r19-f $x) $x)
!(assertEqual (metta (r19-f $t) $t &self) B)

; Repair #21: variables stored in type annotations have private identity.
; A caller binding with the same printed name must not capture the annotation
; candidate when type-cast consumes it.
(: r21-a $t)
!(assertEqual (let $t A (metta r21-a B &self)) r21-a)

; Candidate-private assignments never leak back into an unrelated public
; variable with the same spelling.
(: r21-private $u)
!(assertEqual (let $x (metta r21-private B &self) $u) $u)

; Ground failures retain the exact published diagnostic after freshening.
(: r21-ground A)
!(assertEqual (metta r21-ground B &self)
  (Error r21-ground (BadType B A)))

; Repair #24: success-priority recognizes every expression headed by `Error`,
; not only the conventional three-element diagnostic form.  The nullary error
; alternative is suppressed when the same application also yields a success.
(: Error (-> %Undefined%))
(= (r24-error-head) (Error))
(= (r24-error-head) r24-ok)
!(assertEqual (r24-error-head) r24-ok)

; Repair #26: the expected-aware worker must retain applicability bindings
; that are visible only through the caller's expected type.  The nullary
; application has no argument-variable scope, so `$t = B` specifically guards
; the continuation projection rather than ordinary argument propagation.
(: r26-f (-> B))
(= (r26-f) r26-a)
!(assertEqual
  (chain (metta (r26-f) $t &self) $res (: $res $t))
  (: r26-a B))
