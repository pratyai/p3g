(declare-fun M () Int)
(declare-fun i () Int)
(declare-fun j_0 () Int)
(declare-fun j_1 () Int)

(assert (and
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= (+ i 2) j_1))
      (not (<= j_0 (- M 1)))
      (not (<= (+ i 1) j_0))
      (not (<= j_1 (- M 1)))
      (not (= i (+ i 1)))
      (not (= j_0 j_1))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= (+ i 2) j_1))
      (not (<= j_0 (- M 1)))
      (not (<= (+ i 1) j_0))
      (not (<= j_1 (- M 1)))
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
    )
  )
  (and
    (<= (+ i 2) j_1)
    (<= j_0 (- M 1))
    (<= (+ i 1) j_0)
    (<= j_1 (- M 1))
    (<= 1 (- M 2))
    (<= 0 i)
    (<= (+ i 1) (- M 2))
  )
))

(check-sat)