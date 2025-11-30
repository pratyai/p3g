(declare-fun M () Int)

(assert (forall ((N Int) (i Int))
  (=>
    (and
      (<= (+ i 1) (- N 1))
      (not (or (exists ((j_0 Int)(j_1 Int)(k_1 Int)) (and (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_1) (<= k_1 (- M 1)) (<= j_0 i) (<= 0 j_0) (<= 0 j_1))) (exists ((j_0 Int)(k_0 Int)(j_1 Int)(k_1 Int)) (and (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_1) (<= k_1 (- M 1)) (<= 0 k_0) (<= k_0 (- M 1)) (<= j_0 i) (<= 0 j_0) (<= 0 j_1))) (exists ((j_0 Int)(k_0 Int)(j_1 Int)) (and (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_0) (<= k_0 (- M 1)) (<= j_0 i) (<= 0 j_0) (<= 0 j_1))) (exists ((j_0 Int)(j_1 Int)) (and (<= j_1 (+ i 1)) (= i (+ i 1)) (= j_0 j_1) (<= j_0 i) (<= 0 j_0) (<= 0 j_1)))))
      (<= 1 (- N 1))
      (<= 0 i)
    )
    false
  )
))

(check-sat)