(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun i () Int)

(assert (and
  (forall ((j_0 Int) (j_1 Int) (k_0 Int) (k_1 Int))
    (or
      (not (<= 1 j_0))
      (not (<= 1 k_0))
      (not (<= k_1 (+ N (- 2))))
      (not (<= 1 j_1))
      (not (<= j_1 (+ N (- 2))))
      (not (<= 1 k_1))
      (not (<= k_0 (+ N (- 2))))
      (not (<= j_0 (+ N (- 2))))
      (not (= i (+ i 1)))
      (not (= j_0 j_1))
      (not (= k_0 k_1))
    )
  )
  (and
    (<= (+ i 1) (+ N (- 2)))
    (<= 2 (+ N (- 2)))
    (<= 1 i)
    (<= 2 (+ TSTEPS (- 1)))
  )
))

(check-sat)