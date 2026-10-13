; SPDX-FileCopyrightText: 2026 LeaTTa contributors
; SPDX-License-Identifier: Apache-2.0

; These expectations were checked with the Hyperon 0.2.10 release.

; Numeric matching compares values across the integer and float constructors.
!(assertEqual (unify 1 1.0 hit miss) hit)

; Matching rejects cycles and conflicting assignments to an equality class.
!(assertEqual (unify $x (f $x) hit miss) miss)
!(assertEqual (unify ($x $x) (A B) hit miss) miss)
!(assertEqual (unify ($x $x) (A A) $x miss) A)

; A changed terminal argument stops its branch before later arguments run.
(: he-terminal (-> %Undefined% %Undefined% Atom))
(= (he-to-empty) Empty)
(= (he-to-error) (Error e reason))
!(assertEqualToResult (he-terminal (he-to-empty) (he-to-error)) ())
!(assertEqual (he-terminal (he-to-error) (he-to-empty)) (Error e reason))

; Quoted terminal atoms remain data when argument evaluation leaves them unchanged.
(: he-preserve (-> Atom Atom))
(= (he-preserve $x) (he-boxed $x))
!(assertEqualToResult (he-preserve Empty) ((he-boxed Empty)))
!(assertEqualToResult (he-preserve (Error e reason)) ((he-boxed (Error e reason))))

; An operator expression is evaluated before its application is reduced.
(: (he-operator-thunk) (-> A R))
(: he-choose (-> A R))
(: he-a A)
(: he-hit R)
(= (he-operator-thunk) he-choose)
(= (he-choose he-a) he-hit)
!(assertEqual (metta ((he-operator-thunk) he-a) R &self) he-hit)

; The minimal context-space instruction returns a grounded SpaceType handle.
!(assertEqual
  (eval (chain (context-space) $ctx
    (metta (get-metatype $ctx) %Undefined% &self)))
  Grounded)
!(assertEqual
  (eval (chain (context-space) $ctx
    (metta (get-type $ctx) %Undefined% &self)))
  SpaceType)
