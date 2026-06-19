; Regression for add-reduct / add-atoms / add-reducts space population.
!(bind! &rt (new-space))
!(add-reduct &rt (+ 10 5))
!(add-atoms &rt (p q))
!(assertEqualToResult (get-atoms &rt) (15 p q))
!(bind! &rt2 (new-space))
!(add-reducts &rt2 (a b c))
!(assertEqualToResult (get-atoms &rt2) (a b c))
