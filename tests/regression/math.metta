; SPDX-FileCopyrightText: 2026 MesTTo
; SPDX-License-Identifier: Apache-2.0

; Regression test for the *-math grounded ops (Hyperon runner/stdlib/math.rs).
!(assertEqual (sqrt-math 4.0) 2.0)
!(assertEqual (pow-math 2.0 10.0) 1024.0)
!(assertEqual (log-math 2.0 8.0) 3.0)
!(assertEqual (abs-math -5) 5)
!(assertEqual (abs-math -2.5) 2.5)
!(assertEqual (ceil-math 2.3) 3.0)
!(assertEqual (floor-math 2.7) 2.0)
!(assertEqual (round-math 2.5) 3.0)
!(assertEqual (trunc-math -2.7) -2.0)
!(assertEqual (isnan-math 1.0) False)
!(assertEqual (isinf-math 5) False)
!(assertEqual (+ (sqrt-math 9.0) 1.0) 4.0)
