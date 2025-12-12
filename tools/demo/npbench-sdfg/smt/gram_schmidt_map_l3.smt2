

(assert (forall ((M Int) (N Int) (j Int) (k Int))
  (=>
    (and
      (<= 1 (+ M (- 1)))
      (<= (+ k 2) (+ N (- 1)))
      (<= 1 (+ N (- 1)))
      (<= (+ j 1) (+ N (- 1)))
      (<= (+ k 1) j)
      (not (or (exists ((i_sub_0 Int)) (and (= j (+ j 1)) (<= 0 i_sub_0) (<= i_sub_0 (+ M (- 1))))) (= j (+ j 1)) (exists ((i_sub_0 Int)(i_sub_1 Int)) (and (= i_sub_0 i_sub_1) (<= i_sub_1 (+ M (- 1))) (= j (+ j 1)) (<= 0 i_sub_1) (<= i_sub_0 (+ M (- 1))) (<= 0 i_sub_0))) (exists ((i_dot_0 Int)(i_sub_1 Int)) (and (<= i_sub_1 (+ M (- 1))) (= j (+ j 1)) (<= 0 i_dot_0) (<= 0 i_sub_1) (= i_dot_0 i_sub_1) (<= i_dot_0 (+ M (- 1))))) (exists ((i_dot_1 Int)) (and (= j (+ j 1)) (<= i_dot_1 (+ M (- 1))) (<= 0 i_dot_1))) (exists ((i_sub_1 Int)) (and (<= 0 i_sub_1) (= j (+ j 1)) (<= i_sub_1 (+ M (- 1))))) (exists ((i_dot_0 Int)) (and (= j (+ j 1)) (<= 0 i_dot_0) (<= i_dot_0 (+ M (- 1))))) (exists ((i_sub_0 Int)(i_dot_1 Int)) (and (= j (+ j 1)) (<= 0 i_dot_1) (<= i_dot_1 (+ M (- 1))) (<= i_sub_0 (+ M (- 1))) (<= 0 i_sub_0) (= i_sub_0 i_dot_1))) (exists ((i_dot_0 Int)(i_dot_1 Int)) (and (= j (+ j 1)) (<= 0 i_dot_1) (<= i_dot_1 (+ M (- 1))) (<= 0 i_dot_0) (<= i_dot_0 (+ M (- 1)))))))
    )
    false
  )
))

(check-sat)