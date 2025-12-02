

(assert (forall ((M Int) (N Int) (i Int))
  (=>
    (and
      (not (or (exists ((j_1 Int)(j_0 Int)) (and (<= (+ i 2) j_1) (<= j_0 (- M 1)) (<= (+ i 1) j_0) (<= j_1 (- M 1)) (or (and (= i j_1) (= j_0 (+ i 1))) (and (= i (+ i 1)) (= j_0 j_1))))) (exists ((j_1 Int)(j_0 Int)) (and (<= (+ i 2) j_1) (<= j_0 (- M 1)) (<= (+ i 1) j_0) (<= j_1 (- M 1)) (= i (+ i 1)) (= j_0 j_1)))))
      (<= (+ i 2) (- M 1))
      (<= 1 (- M 2))
      (<= 0 i)
      (<= (+ i 1) (- M 2))
    )
    false
  )
))

(check-sat)