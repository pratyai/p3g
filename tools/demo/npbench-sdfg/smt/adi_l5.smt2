

(assert (forall ((N Int) (TSTEPS Int) (j Int))
  (=>
    (and
      (<= (+ N (- 2)) j)
      (<= (+ j 1) 1)
      (not (exists ((i_0 Int)(i_1 Int)) (and (<= 1 i_0) (or (and (= i_0 i_1) (= j (+ j 2))) (= i_0 i_1) (and (= j (+ j 1)) (= i_0 i_1))) (<= 1 i_1) (<= i_1 (+ N (- 2))) (<= i_0 (+ N (- 2))))))
      (<= 2 (+ N (- 2)))
      (<= (+ N (- 1)) 1)
      (<= 2 TSTEPS)
    )
    false
  )
))

(check-sat)