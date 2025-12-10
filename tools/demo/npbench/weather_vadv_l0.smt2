

(assert (forall ((I Int) (J Int) (K Int) (TSTEPS Int) (t Int))
  (=>
    (and
      (<= 0 t)
      (<= (+ t 1) (- TSTEPS 1))
      (<= 1 (- K 1))
      (<= 1 (- J 1))
      (<= 1 (- I 1))
      (<= 1 (- TSTEPS 1))
      (not (or (exists ((i_loop_0 Int)(j_loop_0 Int)(k_loop_0 Int)(i_loop_1 Int)(j_loop_1 Int)(k_loop_1 Int)) (and (<= 0 i_loop_0) (<= i_loop_0 (- I 1)) (<= 0 j_loop_0) (<= j_loop_0 (- J 1)) (<= 0 k_loop_0) (<= k_loop_0 (- K 1)) (or (and (= i_loop_0 (+ i_loop_1 1)) (= j_loop_0 j_loop_1) (= k_loop_0 k_loop_1)) (and (= i_loop_0 i_loop_1) (= j_loop_0 j_loop_1) (= k_loop_0 k_loop_1))) (<= 0 i_loop_1) (<= i_loop_1 (- I 1)) (<= 0 j_loop_1) (<= j_loop_1 (- J 1)) (<= 0 k_loop_1) (<= k_loop_1 (- K 1)))) (exists ((i_loop_0 Int)(j_loop_0 Int)(k_loop_0 Int)(i_loop_1 Int)(j_loop_1 Int)(k_loop_1 Int)) (and (= i_loop_0 i_loop_1) (= j_loop_0 j_loop_1) (= k_loop_0 k_loop_1) (<= 0 i_loop_0) (<= i_loop_0 (- I 1)) (<= 0 j_loop_0) (<= j_loop_0 (- J 1)) (<= 0 k_loop_0) (<= k_loop_0 (- K 1)) (<= 0 i_loop_1) (<= i_loop_1 (- I 1)) (<= 0 j_loop_1) (<= j_loop_1 (- J 1)) (<= 0 k_loop_1) (<= k_loop_1 (- K 1)))) (exists ((i_loop_0 Int)(j_loop_0 Int)(k_loop_0 Int)(i_loop_1 Int)(j_loop_1 Int)(k_loop_1 Int)) (and (= k_loop_0 k_loop_1) (<= 0 i_loop_0) (<= i_loop_0 (- I 1)) (<= 0 j_loop_0) (<= j_loop_0 (- J 1)) (<= 0 k_loop_0) (<= k_loop_0 (- K 1)) (= (+ i_loop_0 1) (+ i_loop_1 1)) (<= 0 i_loop_1) (<= i_loop_1 (- I 1)) (= (+ j_loop_0 1) (+ j_loop_1 1)) (<= 0 j_loop_1) (<= j_loop_1 (- J 1)) (<= 0 k_loop_1) (<= k_loop_1 (- K 1)))) (exists ((i_loop_0 Int)(j_loop_0 Int)(k_loop_0 Int)(i_loop_1 Int)(j_loop_1 Int)(k_loop_1 Int)) (and (<= 0 i_loop_0) (<= i_loop_0 (- I 1)) (<= 0 j_loop_0) (<= j_loop_0 (- J 1)) (<= 0 k_loop_0) (<= k_loop_0 (- K 1)) (<= 0 i_loop_1) (<= i_loop_1 (- I 1)) (<= 0 j_loop_1) (<= j_loop_1 (- J 1)) (or (and (= j_loop_0 j_loop_1) (= (+ i_loop_0 1) i_loop_1) (= k_loop_0 k_loop_1)) (and (= i_loop_0 i_loop_1) (= j_loop_0 j_loop_1) (= k_loop_0 k_loop_1))) (<= 0 k_loop_1) (<= k_loop_1 (- K 1))))))
    )
    false
  )
))

(check-sat)