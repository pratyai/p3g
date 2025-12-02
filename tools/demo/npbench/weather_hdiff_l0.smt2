

(assert (forall ((I Int) (J Int) (K Int) (i_loop Int))
  (=>
    (and
      (<= 0 i_loop)
      (<= (+ i_loop 1) (- (+ I 2) 1))
      (not (exists ((j_loop_1 Int)(k_loop_0 Int)(j_loop_0 Int)(k_loop_1 Int)) (and (= i_loop (+ i_loop 1)) (= j_loop_0 j_loop_1) (= k_loop_0 k_loop_1) (<= 0 j_loop_0) (<= j_loop_0 (- (+ J 2) 1)) (<= 0 k_loop_0) (<= k_loop_0 (- K 1)) (<= 0 j_loop_1) (<= j_loop_1 (- (+ J 2) 1)) (<= 0 k_loop_1) (<= k_loop_1 (- K 1)))))
      (<= 1 (- K 1))
      (<= 1 (- (+ J 2) 1))
      (<= 1 (- (+ I 2) 1))
    )
    false
  )
))

(check-sat)