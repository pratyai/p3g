(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun j () Int)

(assert (and
  (and
    (<= 2 TSTEPS)
    (<= (+ N (- 2)) j)
    (<= (+ j 1) 1)
    (<= 2 (+ N (- 2)))
    (<= (+ N (- 1)) 1)
  )
  (forall ((i_0 Int) (i_1 Int))
    (or
      (not (<= 1 i_0))
      (and
        (or
          (not (= j (+ j 2)))
          (not (= i_0 i_1))
        )
        (not (= i_0 i_1))
        (or
          (not (= j (+ j 1)))
          (not (= i_0 i_1))
        )
      )
      (not (<= 1 i_1))
      (not (<= i_1 (+ N (- 2))))
      (not (<= i_0 (+ N (- 2))))
    )
  )
))

(check-sat)