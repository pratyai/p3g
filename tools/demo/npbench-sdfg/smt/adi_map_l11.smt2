

(assert (forall ((N Int) (TSTEPS Int) (j Int))
  (=>
    (and
      (<= 1 j)
      (<= 2 (+ N (- 2)))
      (<= 2 TSTEPS)
      (<= (+ j 1) (+ N (- 2)))
      (not (exists ((i_1 Int)(i_0 Int)) (and (or (and (= (- (+ N (- 2)) j) (- (+ N (- 1)) (+ j 1))) (= i_0 i_1)) (and (= (- (+ N (- 2)) j) (- (+ N (- 2)) (+ j 1))) (= i_0 i_1)) (and (= (- (+ N (- 1)) j) (- (+ N (- 2)) (+ j 1))) (= i_0 i_1))) (<= i_1 (+ N (- 2))) (<= i_0 (+ N (- 2))) (<= 1 i_0) (<= 1 i_1))))
    )
    false
  )
))

(check-sat)