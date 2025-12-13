

(assert (forall ((N Int) (TSTEPS Int) (i Int))
  (=>
    (and
      (<= (+ i 1) (+ N (- 2)))
      (not (exists ((j_0 Int)(j_1 Int)(k_0 Int)(k_1 Int)) (and (<= 1 j_0) (<= 1 k_0) (<= k_1 (+ N (- 2))) (<= 1 j_1) (<= j_1 (+ N (- 2))) (<= 1 k_1) (<= k_0 (+ N (- 2))) (<= j_0 (+ N (- 2))) (= i (+ i 1)) (= j_0 j_1) (= k_0 k_1))))
      (<= 2 (+ N (- 2)))
      (<= 1 i)
      (<= 2 (+ TSTEPS (- 1)))
    )
    false
  )
))

(check-sat)