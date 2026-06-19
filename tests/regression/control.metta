; Regression for capture (nondeterminism control) + for-each-in-atom.
!(assertEqual (capture (+ 1 2)) 3)
!(assertEqualToResult (capture (superpose (1 2 3))) (1 2 3))
