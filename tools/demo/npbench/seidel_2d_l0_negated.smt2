(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun t () Int)

(assert (and
  (and
    (<= (+ t 1) (- TSTEPS 2))
    (<= 2 (- N 2))
    (<= 1 (- TSTEPS 2))
    (<= 0 t)
  )
  (forall ((i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int))
    (or
      (not (<= 1 j_0))
      (not (<= j_0 (- N 2)))
      (not (<= 1 i_1))
      (not (<= i_1 (- N 2)))
      (not (<= 1 j_1))
      (not (<= j_1 (- N 2)))
      (not (<= i_0 (- N 2)))
      (not (<= 1 i_0))
      (and
        (or
          (not (= j_0 (- j_1 1)))
          (not (= i_0 (+ i_1 1)))
        )
        (or
          (not (= j_0 (+ j_1 1)))
          (not (= i_0 i_1))
        )
        (or
          (not (= i_0 i_1))
          (not (= j_0 j_1))
        )
        (or
          (not (= j_0 (+ j_1 1)))
          (not (= i_0 (- i_1 1)))
        )
        (or
          (not (= j_0 j_1))
          (not (= i_0 (- i_1 1)))
        )
        (or
          (not (= j_0 (- j_1 1)))
          (not (= i_0 (- i_1 1)))
        )
        (or
          (not (= i_0 (+ i_1 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (= i_0 (+ i_1 1)))
          (not (= j_0 (+ j_1 1)))
        )
      )
    )
  )
  (forall ((i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int))
    (or
      (not (<= 1 j_0))
      (not (<= j_0 (- N 2)))
      (not (<= 1 i_1))
      (not (<= i_1 (- N 2)))
      (and
        (or
          (not (= (- i_0 1) i_1))
          (not (= j_0 j_1))
        )
        (or
          (not (= (+ j_0 1) j_1))
          (not (= (- i_0 1) i_1))
        )
        (or
          (not (= i_0 i_1))
          (not (= j_0 j_1))
        )
        (or
          (not (= (- j_0 1) j_1))
          (not (= (+ i_0 1) i_1))
        )
        (or
          (not (= (+ j_0 1) j_1))
          (not (= (+ i_0 1) i_1))
        )
        (or
          (not (= j_0 j_1))
          (not (= (+ i_0 1) i_1))
        )
        (or
          (not (= (- i_0 1) i_1))
          (not (= (- j_0 1) j_1))
        )
        (or
          (not (= (+ j_0 1) j_1))
          (not (= i_0 i_1))
        )
      )
      (not (<= 1 j_1))
      (not (<= j_1 (- N 2)))
      (not (<= 1 i_0))
      (not (<= i_0 (- N 2)))
    )
  )
  (forall ((i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int))
    (or
      (not (<= 1 j_0))
      (not (<= j_0 (- N 2)))
      (not (<= 1 i_1))
      (not (<= i_1 (- N 2)))
      (not (<= 1 j_1))
      (not (<= j_1 (- N 2)))
      (not (= i_0 i_1))
      (not (= j_0 j_1))
      (not (<= 1 i_0))
      (not (<= i_0 (- N 2)))
    )
  )
  (forall ((i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int))
    (or
      (not (<= 1 j_0))
      (not (<= j_0 (- N 2)))
      (not (<= 1 i_1))
      (not (<= i_1 (- N 2)))
      (not (<= 1 j_1))
      (not (<= j_1 (- N 2)))
      (and
        (or
          (not (= j_0 (- j_1 1)))
          (not (= i_0 i_1))
        )
        (or
          (not (= (- j_0 1) j_1))
          (not (= i_0 i_1))
        )
        (or
          (not (= i_0 i_1))
          (not (= j_0 j_1))
        )
      )
      (not (<= 1 i_0))
      (not (<= i_0 (- N 2)))
    )
  )
))

(check-sat)