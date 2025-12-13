(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun j () Int)

(assert (and
  (and
    (<= 2 (+ N (- 2)))
    (<= 2 (+ TSTEPS (- 1)))
    (<= (+ j 1) (+ N (- 2)))
    (<= 1 j)
  )
  (forall ((k_0 Int) (k_1 Int))
    (or
      (not (<= k_0 (+ N (- 2))))
      (not (<= 1 k_0))
      (not (<= 1 k_1))
      (not (= j (+ j 1)))
      (not (= k_0 k_1))
      (not (<= k_1 (+ N (- 2))))
    )
  )
))

(check-sat)