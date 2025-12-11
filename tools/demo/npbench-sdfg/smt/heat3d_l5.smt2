

(assert (forall ((N Int) (TSTEPS Int) (j Int))
  (=>
    (and
      (<= 2 (+ N (- 2)))
      (<= 2 (+ TSTEPS (- 1)))
      (<= (+ j 1) (+ N (- 2)))
      (not (exists ((k_0 Int)(k_1 Int)) (and (<= k_0 (+ N (- 2))) (<= 1 k_0) (<= 1 k_1) (= j (+ j 1)) (= k_0 k_1) (<= k_1 (+ N (- 2))))))
      (<= 1 j)
    )
    false
  )
))

(check-sat)