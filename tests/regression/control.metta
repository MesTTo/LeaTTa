; SPDX-FileCopyrightText: 2026 MesTTo
; SPDX-License-Identifier: Apache-2.0

; Regression for capture (nondeterminism control) + for-each-in-atom.
!(assertEqual (capture (+ 1 2)) 3)
!(assertEqualToResult (capture (superpose (1 2 3))) (1 2 3))

; Repair #22: collapse-bind stores each alternative's bindings in an opaque grounded payload,
; and superpose-bind restores them before continuing.
(= (collapse-binding-probe A) Hit)
!(assertEqual
  (chain (collapse-bind (eval (collapse-binding-probe $q))) $collapsed
    (chain (superpose-bind $collapsed) $result $q))
  A)

; A restored binding must still be reconciled with bindings established after collapse.
; The conflicting $q = A and $q = B alternatives are rejected rather than leaked.
!(assertEqualToResult
  (chain (collapse-bind (eval (collapse-binding-probe $q))) $collapsed
    (unify B $q (superpose-bind $collapsed) fallback))
  ())
