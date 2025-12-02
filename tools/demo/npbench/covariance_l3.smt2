

(assert (forall ((M Int) (N Int) (i Int))
  (=>
    (and
      (not (or (exists ((j_0 Int)(j_1 Int)) (and (= i (+ i 1)) (= j_0 j_1) (<= i j_0) (<= j_0 (- M 1)) (<= (+ i 1) j_1) (<= j_1 (- M 1)))) (exists ((j_0 Int)(j_1 Int)) (and (or (and (= i j_1) (= j_0 (+ i 1))) (and (= i (+ i 1)) (= j_0 j_1))) (<= i j_0) (<= j_0 (- M 1)) (<= (+ i 1) j_1) (<= j_1 (- M 1))))))
      (<= 0 i)
      (<= 1 (- M 1))
      (<= (+ i 1) (- M 1))
    )
    false
  )
))

(check-sat)