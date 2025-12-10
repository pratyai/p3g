(declare-fun M () Int)
(declare-fun i () Int)

(assert (and
  (and
    (<= (+ i 1) (- M 1))
    (<= 1 (- M 1))
    (<= 0 i)
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (= i (+ i 1)))
      (not (= j_0 j_1))
      (not (<= i j_0))
      (not (<= j_0 (- M 1)))
      (not (<= (+ i 1) j_1))
      (not (<= j_1 (- M 1)))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (and
        (or
          (not (= i j_1))
          (not (= j_0 (+ i 1)))
        )
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
      )
      (not (<= i j_0))
      (not (<= j_0 (- M 1)))
      (not (<= (+ i 1) j_1))
      (not (<= j_1 (- M 1)))
    )
  )
))

(check-sat)