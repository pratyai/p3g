(declare-fun H () Int)
(declare-fun W () Int)
(declare-fun j () Int)

(assert (and
  (forall ((i_0 Int) (i_1 Int))
    (or
      (not (<= 0 i_0))
      (not (<= i_0 (- W 1)))
      (not (<= 0 i_1))
      (not (<= i_1 (- W 1)))
      (and
        (or
          (not (= (- j 2) (+ j 1)))
          (not (= i_0 i_1))
        )
        (or
          (not (= i_0 i_1))
          (not (= j (- (+ j 1) 1)))
        )
        (or
          (not (= i_0 i_1))
          (not (= j (- (+ j 1) 2)))
        )
        (or
          (not (= i_0 i_1))
          (not (= j (+ j 1)))
        )
        (or
          (not (= i_0 i_1))
          (not (= (- j 1) (+ j 1)))
        )
      )
    )
  )
  (and
    (<= 2 j)
    (<= (+ j 1) (- H 1))
    (<= 1 (- W 1))
    (<= 3 (- H 1))
  )
))

(check-sat)