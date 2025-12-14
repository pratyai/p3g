(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun j () Int)

(assert (and
  (forall ((i_0 Int) (i_1 Int))
    (or
      (and
        (or
          (not (= (- (+ N (- 2)) j) (- (+ N (- 1)) (+ j 1))))
          (not (= i_0 i_1))
        )
        (or
          (not (= (- (+ N (- 2)) j) (- (+ N (- 2)) (+ j 1))))
          (not (= i_0 i_1))
        )
        (or
          (not (= (- (+ N (- 1)) j) (- (+ N (- 2)) (+ j 1))))
          (not (= i_0 i_1))
        )
      )
      (not (<= i_1 (+ N (- 2))))
      (not (<= i_0 (+ N (- 2))))
      (not (<= 1 i_0))
      (not (<= 1 i_1))
    )
  )
  (and
    (<= 1 j)
    (<= 2 (+ N (- 2)))
    (<= 2 TSTEPS)
    (<= (+ j 1) (+ N (- 2)))
  )
))

(check-sat)