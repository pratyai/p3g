

(assert (forall ((NX Int) (NY Int) (TMAX Int) (t Int))
  (=>
    (and
      (<= 0 t)
      (<= (+ t 1) (- TMAX 1))
      (<= 1 (- NY 2))
      (<= 1 (- NX 2))
      (<= 2 (- NY 1))
      (<= 1 (- NX 1))
      (<= 1 (- NY 1))
      (<= 2 (- NX 1))
      (<= 1 (- TMAX 1))
      (not (or (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (<= 0 j_0) (<= 0 j_1) (<= j_1 (- NY 1)) (<= i_0 (- NX 2)) (<= j_0 (- NY 2)) (or (and (= j_0 j_1) (= i_0 (- i_1 1))) (and (= (+ i_0 1) i_1) (= j_0 j_1)) (and (= i_0 i_1) (= j_0 j_1))) (<= 1 i_1) (<= i_1 (- NX 1)) (<= 0 i_0))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)) (and (or (and (= j_0 j_1) (= i_0 0)) (and (= (+ i_0 1) 0) (= j_0 j_1))) (<= 0 j_0) (<= 0 j_1) (<= j_1 (- NY 1)) (<= i_0 (- NX 2)) (<= j_0 (- NY 2)) (<= 0 i_0))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (or (and (= i_0 i_1) (= j_0 j_1)) (and (= i_0 i_1) (= j_0 (- j_1 1))) (and (= (+ j_0 1) j_1) (= i_0 i_1))) (<= 1 j_1) (<= 0 j_0) (<= j_1 (- NY 1)) (<= i_0 (- NX 2)) (<= j_0 (- NY 2)) (<= i_1 (- NX 1)) (<= 0 i_1) (<= 0 i_0))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (<= i_1 (- NX 2)) (<= j_1 (- NY 2)) (<= 0 j_0) (<= 0 j_1) (<= i_0 (- NX 2)) (= i_0 i_1) (<= j_0 (- NY 2)) (= j_0 j_1) (<= 0 i_1) (<= 0 i_0))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= 1 i_0) (<= i_0 (- NX 1)) (<= j_0 (- NY 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= i_0 0) (= j_0 j_1))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (<= 0 j_0) (<= 1 i_0) (<= i_0 (- NX 1)) (<= j_0 (- NY 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= i_0 i_1) (= j_0 j_1) (<= 1 i_1) (<= i_1 (- NX 1)))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (<= i_1 (- NX 2)) (<= j_1 (- NY 2)) (or (and (= i_0 i_1) (= j_0 j_1)) (and (= (- i_0 1) i_1) (= j_0 j_1)) (and (= j_0 j_1) (= i_0 (+ i_1 1)))) (<= 1 i_0) (<= 0 j_0) (<= i_0 (- NX 1)) (<= j_0 (- NY 1)) (<= 0 j_1) (<= 0 i_1))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (<= 1 j_0) (<= 1 j_1) (<= j_0 (- NY 1)) (<= i_0 (- NX 1)) (<= j_1 (- NY 1)) (= i_0 i_1) (= j_0 j_1) (<= i_1 (- NX 1)) (<= 0 i_1) (<= 0 i_0))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)(i_1 Int)) (and (<= i_1 (- NX 2)) (<= 1 j_0) (<= j_1 (- NY 2)) (<= i_0 (- NX 1)) (<= j_0 (- NY 1)) (<= 0 j_1) (or (and (= i_0 i_1) (= j_0 (+ j_1 1))) (and (= i_0 i_1) (= j_0 j_1)) (and (= i_0 i_1) (= (- j_0 1) j_1))) (<= 0 i_1) (<= 0 i_0))) (exists ((j_0 Int)(j_1 Int)(i_1 Int)) (and (<= i_1 (- NX 2)) (<= j_1 (- NY 2)) (or (and (= j_0 j_1) (= 0 i_1)) (and (= j_0 j_1) (= 0 (+ i_1 1)))) (<= 0 j_0) (<= j_0 (- NY 1)) (<= 0 j_1) (<= 0 i_1))) (exists ((j_0 Int)(j_1 Int)(i_1 Int)) (and (<= 0 j_0) (<= j_0 (- NY 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= j_0 j_1) (<= 1 i_1) (<= i_1 (- NX 1)) (= 0 i_1))) (exists ((j_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NY 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= j_0 j_1)))))
    )
    false
  )
))

(check-sat)