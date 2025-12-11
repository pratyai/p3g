

(assert (forall ((N Int) (TSTEPS Int) (j Int))
  (=>
    (and
      (<= 1 j)
      (<= 2 (+ N (- 2)))
      (<= 2 TSTEPS)
      (<= (+ j 1) (+ N (- 2)))
      (not (or (exists ((i_1 Int)(i_0 Int)) (and (<= 1 i_0) (<= 1 i_1) (or (and (= i_0 i_1) (= (+ j (- 1)) (+ j 1))) (and (= j (+ j 1)) (= i_0 i_1)) (= i_0 i_1)) (<= i_1 (+ N (- 2))) (<= i_0 (+ N (- 2))))) (exists ((i_1 Int)(i_0 Int)) (and (<= 1 i_0) (<= 1 i_1) (= i_0 i_1) (<= i_1 (+ N (- 2))) (<= i_0 (+ N (- 2))))) (exists ((i_1 Int)(i_0 Int)) (and (<= 1 i_0) (<= 1 i_1) (= (+ j (- 1)) (+ j 1)) (= i_0 i_1) (<= i_1 (+ N (- 2))) (<= i_0 (+ N (- 2)))))))
    )
    false
  )
))

(check-sat)