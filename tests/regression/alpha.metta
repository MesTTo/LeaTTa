; SPDX-FileCopyrightText: 2026 MesTTo
; SPDX-License-Identifier: Apache-2.0

; Regression: if-equal / unique-atom / =alpha now compare up to alpha-equivalence.
!(assertEqual (if-equal a a yes no) yes)
!(assertEqual (if-equal a b yes no) no)
!(assertEqual (if-equal (foo $x) (foo $y) yes no) yes)
!(assertEqual (=alpha ($x) ($y)) True)
!(assertEqual (=alpha a a) True)
!(assertEqual (=alpha (f a) (f b)) False)
!(assertEqual (unique-atom (1 2 1 3 2)) (1 2 3))
