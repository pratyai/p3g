(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun j () Int)

(assert (and
  (forall ((i_0 Int) (i_1 Int))
    (or
      (not (<= 1 i_0))
      (not (<= 1 i_1))
      (not (= (+ j (- 1)) (+ j 1)))
      (not (= i_0 i_1))
      (not (<= i_1 (+ N (- 2))))
      (not (<= i_0 (+ N (- 2))))
    )
  )
  (forall ((i_0 Int) (i_1 Int))
    (or
      (not (<= 1 i_0))
      (not (<= 1 i_1))
      (not (= i_0 i_1))
      (not (<= i_1 (+ N (- 2))))
      (not (<= i_0 (+ N (- 2))))
    )
  )
  (forall ((i_0 Int) (i_1 Int))
    (or
      (not (<= 1 i_0))
      (not (<= 1 i_1))
      (and
        (or
          (not (= i_0 i_1))
          (not (= (+ j (- 1)) (+ j 1)))
        )
        (not (= i_0 i_1))
        (or
          (not (= i_0 i_1))
          (not (= j (+ j 1)))
        )
      )
      (not (<= i_1 (+ N (- 2))))
      (not (<= i_0 (+ N (- 2))))
    )
  )
  (and
    (<= 2 TSTEPS)
    (<= (+ j 1) (+ N (- 2)))
    (<= 1 j)
    (<= 2 (+ N (- 2)))
  )
))

(check-sat)