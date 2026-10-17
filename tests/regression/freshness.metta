; SPDX-License-Identifier: Apache-2.0

; Capture-avoidance regression: the incoming binding uses the exact spelling that legacy
; counter-zero rule freshening assigned to $x. The rule must still fire under that binding.
(= (freshness-probe $x) $x)
!(assertEqual (unify b $x#0 (freshness-probe a) fallback) a)
