

(assert (forall ((M Int) (N Int) (i Int))
  (=>
    (and
      (<= 1 i)
      (<= 1 (- M 1))
      (<= 1 (- N 1))
      (<= 0 i)
      (<= (+ i 1) (- N 1))
      (not (or (exists ((j_1 Int)(k_1 Int)(j_0 Int)) (and (<= 0 j_1) (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_1) (<= k_1 (- M 1)) (<= j_0 i) (<= 0 j_0))) (exists ((j_1 Int)(j_0 Int)) (and (<= 0 j_1) (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= j_0 i) (<= 0 j_0))) (exists ((j_1 Int)(k_1 Int)(j_0 Int)(k_0 Int)) (and (<= 0 j_1) (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_1) (<= k_1 (- M 1)) (<= 0 k_0) (<= k_0 (- M 1)) (<= j_0 i) (<= 0 j_0))) (exists ((j_1 Int)(j_0 Int)(k_0 Int)) (and (<= 0 j_1) (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_0) (<= k_0 (- M 1)) (<= j_0 i) (<= 0 j_0)))))
    )
    false
  )
))

(check-sat)