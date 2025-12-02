(declare-fun N () Int)
(declare-fun i () Int)

(assert (and
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= 0 j_1))
      (not (<= j_1 (- (+ i 1) 1)))
      (not (<= j_0 (- i 1)))
      (not (<= 0 j_0))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (= i j_1))
          (not (= j_0 j_1))
        )
        (or
          (not (= j_0 (+ i 1)))
          (not (= j_0 j_1))
        )
      )
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= 0 j_1))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) (- i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_1))
          (not (<= j_1 (- i 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (= i j_1))
          (not (= j_0 j_1))
        )
      )
      (not (<= j_1 (- (+ i 1) 1)))
      (not (<= j_0 (- N 1)))
      (not (<= i j_0))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= 0 j_1))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_0))
          (not (<= j_0 (- j_1 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (= j_0 j_1))
          (not (<= 0 i))
          (not (<= i (- j_1 1)))
        )
        (or
          (not (= j_0 (+ i 1)))
          (not (= j_0 j_1))
        )
      )
      (not (<= j_1 (- (+ i 1) 1)))
      (not (<= j_0 (- i 1)))
      (not (<= 0 j_0))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= 0 j_1))
      (not (<= j_1 (- (+ i 1) 1)))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) (- j_0 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (= i j_1))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_1))
          (not (<= j_1 (- j_0 1)))
          (not (= i (+ i 1)))
        )
      )
      (not (<= j_0 (- i 1)))
      (not (<= 0 j_0))
    )
  )
  (and
    (<= (+ i 1) (- N 1))
    (<= 1 (- i 1))
    (<= 1 (- N 1))
    (<= 0 i)
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= (+ i 1) j_1))
      (not (<= j_1 (- N 1)))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= i (- (+ i 1) 1)))
          (not (<= 0 i))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_0))
          (not (<= j_0 (- (+ i 1) 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) (- i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_1))
          (not (<= j_1 (- i 1)))
          (not (= i (+ i 1)))
        )
      )
      (not (<= j_0 (- N 1)))
      (not (<= i j_0))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= 0 j_1))
      (not (<= j_1 (- (+ i 1) 1)))
      (and
        (or
          (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) (- j_0 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_1))
          (not (<= j_1 (- j_0 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (= j_0 j_1))
          (not (<= 0 i))
          (not (<= i (- j_1 1)))
        )
        (or
          (not (<= 0 j_0))
          (not (<= j_0 (- j_1 1)))
          (not (= i (+ i 1)))
        )
      )
      (not (<= j_0 (- i 1)))
      (not (<= 0 j_0))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= (+ i 1) j_1))
      (not (<= j_1 (- N 1)))
      (and
        (or
          (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) (- j_0 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_1))
          (not (<= j_1 (- j_0 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= i (- (+ i 1) 1)))
          (not (<= 0 i))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_0))
          (not (<= j_0 (- (+ i 1) 1)))
          (not (= i (+ i 1)))
        )
      )
      (not (<= j_0 (- i 1)))
      (not (<= 0 j_0))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= (+ i 1) j_1))
      (not (<= j_1 (- N 1)))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_0))
          (not (<= j_0 (- (+ i 1) 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (<= i (- (+ i 1) 1)))
          (not (<= 0 i))
          (not (= j_0 j_1))
        )
        (or
          (not (= j_0 (+ i 1)))
          (not (= j_0 j_1))
        )
      )
      (not (<= j_0 (- i 1)))
      (not (<= 0 j_0))
    )
  )
  (forall ((j_0 Int) (j_1 Int))
    (or
      (not (<= 0 j_1))
      (not (<= j_1 (- (+ i 1) 1)))
      (not (<= j_0 (- N 1)))
      (and
        (or
          (not (= i (+ i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (= j_0 j_1))
          (not (<= 0 i))
          (not (<= i (- j_1 1)))
        )
        (or
          (not (<= 0 (+ i 1)))
          (not (<= (+ i 1) (- i 1)))
          (not (= j_0 j_1))
        )
        (or
          (not (<= 0 j_1))
          (not (<= j_1 (- i 1)))
          (not (= i (+ i 1)))
        )
        (or
          (not (<= 0 j_0))
          (not (<= j_0 (- j_1 1)))
          (not (= i (+ i 1)))
        )
      )
      (not (<= i j_0))
    )
  )
))

(check-sat)