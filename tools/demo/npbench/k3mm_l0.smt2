

(assert (forall ((NI Int) (NJ Int) (NK Int) (NL Int) (NM Int) (i Int))
  (=>
    (and
      (<= 0 i)
      (<= (+ i 1) (- NI 1))
      (not (or (exists ((j_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NJ 1)) (<= 0 j_1) (<= j_1 (- NJ 1)) (= i (+ i 1)) (= j_0 j_1))) (exists ((j_0 Int)(k_0 Int)(j_1 Int)(k_1 Int)) (and (<= 0 j_0) (<= j_0 (- NJ 1)) (<= 0 j_1) (<= j_1 (- NJ 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_1) (<= k_1 (- NK 1)) (<= 0 k_0) (<= k_0 (- NK 1)))) (exists ((j_0 Int)(k_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NJ 1)) (<= 0 j_1) (<= j_1 (- NJ 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_0) (<= k_0 (- NK 1)))) (exists ((j_0 Int)(j_1 Int)(k_1 Int)) (and (<= 0 j_0) (<= j_0 (- NJ 1)) (<= 0 j_1) (<= j_1 (- NJ 1)) (= i (+ i 1)) (= j_0 j_1) (<= 0 k_1) (<= k_1 (- NK 1))))))
      (<= 1 (- NK 1))
      (<= 1 (- NJ 1))
      (<= 1 (- NI 1))
    )
    false
  )
))

(check-sat)