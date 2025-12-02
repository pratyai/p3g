(declare-fun M () Int)
(declare-fun N () Int)
(declare-fun i () Int)

(assert (and
  (forall ((j_0 Int) (j_1 Int))
    (or
      (and
        (or
          (not (<= i (- M 1)))
          (not (= j_0 j_1))
          (not (<= (+ i 2) i))
        )
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (= j_0 j_1))
          (not (<= (+ i 1) (+ i 1)))
          (not (<= (+ i 1) (- M 1)))
        )
      )
      (not (<= 0 j_0))
      (not (<= j_0 (- N 1)))
      (not (<= 0 j_1))
      (not (<= j_1 (- N 1)))
    )
  )
  (and
    (<= 1 (- N 1))
    (<= 0 i)
    (<= (+ i 1) (- M 1))
    (<= 1 (- M 1))
  )
))

(check-sat)