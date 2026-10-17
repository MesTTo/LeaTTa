; SPDX-FileCopyrightText: 2026 MesTTo
; SPDX-License-Identifier: Apache-2.0

; Regression for add-reduct / add-atoms / add-reducts space population.
!(bind! &rt (new-space))
!(add-reduct &rt (+ 10 5))
!(add-atoms &rt (p q))
!(assertEqualToResult (get-atoms &rt) (15 p q))
!(bind! &rt2 (new-space))
!(add-reducts &rt2 (a b c))
!(assertEqualToResult (get-atoms &rt2) (a b c))

; The embedded metta boundary must evaluate in its selected space.  Before
; repair #8 it silently used &self and left r8-local unreduced.
!(bind! &r8-space (new-space))
!(add-atom &r8-space (= (r8-local) r8-result))
!(assertEqual (metta (r8-local) %Undefined% &r8-space) r8-result)
