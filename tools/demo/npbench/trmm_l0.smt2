

(assert (forall ((M Int) (N Int) (i Int))
  (=>
    (and
      (<= 1 (- N 1))
      (<= 1 (- M 1))
      (not (exists ((j_0 Int)(j_1 Int)) (and (or (and (<= i (- M 1)) (= j_0 j_1) (<= (+ i 2) i)) (and (= i (+ i 1)) (= j_0 j_1)) (and (= j_0 j_1) (<= (+ i 1) (+ i 1)) (<= (+ i 1) (- M 1)))) (<= 0 j_0) (<= j_0 (- N 1)) (<= 0 j_1) (<= j_1 (- N 1)))))
      (<= 0 i)
      (<= (+ i 1) (- M 1))
    )
    false
  )
))

(check-sat)