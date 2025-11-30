(declare-fun NX () Int)
(declare-fun NY () Int)

(assert (forall ((TMAX Int) (t Int))
  (=>
    (and
      (<= 1 (- TMAX 1))
      (<= (+ t 1) (- TMAX 1))
      (not (or (exists ((i_1 Int)(j_0 Int)(j_1 Int)) (and (or (and (= j_0 j_1) (= 0 i_1)) (and (= 0 (+ i_1 1)) (= j_0 j_1))) (<= 0 j_0) (<= j_0 (- NY 1)) (<= 0 j_1) (<= 0 i_1) (<= i_1 (- NX 2)) (<= j_1 (- NY 2)))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (<= j_0 (- NY 1)) (<= 0 j_1) (<= i_0 (- NX 1)) (<= 0 i_1) (or (and (= i_0 i_1) (= (- j_0 1) j_1)) (and (= j_0 j_1) (= i_0 i_1)) (and (= j_0 (+ j_1 1)) (= i_0 i_1))) (<= 0 i_0) (<= i_1 (- NX 2)) (<= 1 j_0) (<= j_1 (- NY 2)))) (exists ((j_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NY 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= j_0 j_1))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= 0 j_1) (<= i_0 (- NX 2)) (= j_0 j_1) (<= j_0 (- NY 2)) (= i_0 i_1) (<= 0 i_1) (<= 0 i_0) (<= i_1 (- NX 2)) (<= j_1 (- NY 2)))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_1 (- NY 1)) (<= i_0 (- NX 2)) (<= j_0 (- NY 2)) (<= i_1 (- NX 1)) (<= 0 i_1) (<= 1 j_1) (<= 0 i_0) (or (and (= (+ j_0 1) j_1) (= i_0 i_1)) (and (= j_0 j_1) (= i_0 i_1)) (and (= j_0 (- j_1 1)) (= i_0 i_1))))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= 0 j_1) (<= j_1 (- NY 1)) (<= i_0 (- NX 2)) (<= j_0 (- NY 2)) (<= 1 i_1) (<= i_1 (- NX 1)) (or (and (= j_0 j_1) (= i_0 i_1)) (and (= j_0 j_1) (= i_0 (- i_1 1))) (and (= (+ i_0 1) i_1) (= j_0 j_1))) (<= 0 i_0))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)) (and (or (and (= (+ i_0 1) 0) (= j_0 j_1)) (and (= i_0 0) (= j_0 j_1))) (<= 0 j_0) (<= 0 j_1) (<= j_1 (- NY 1)) (<= i_0 (- NX 2)) (<= j_0 (- NY 2)) (<= 0 i_0))) (exists ((i_1 Int)(j_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NY 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= j_0 j_1) (<= 1 i_1) (<= i_1 (- NX 1)) (= 0 i_1))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (<= j_0 (- NY 1)) (<= i_0 (- NX 1)) (<= j_1 (- NY 1)) (= j_0 j_1) (= i_0 i_1) (<= i_1 (- NX 1)) (<= 0 i_1) (<= 1 j_1) (<= 0 i_0) (<= 1 j_0))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (or (and (= (- i_0 1) i_1) (= j_0 j_1)) (and (= j_0 j_1) (= i_0 i_1)) (and (= i_0 (+ i_1 1)) (= j_0 j_1))) (<= 0 j_0) (<= j_0 (- NY 1)) (<= 1 i_0) (<= i_0 (- NX 1)) (<= 0 j_1) (<= 0 i_1) (<= i_1 (- NX 2)) (<= j_1 (- NY 2)))) (exists ((i_1 Int)(j_0 Int)(i_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NY 1)) (<= 1 i_0) (<= i_0 (- NX 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= j_0 j_1) (= i_0 i_1) (<= 1 i_1) (<= i_1 (- NX 1)))) (exists ((j_0 Int)(i_0 Int)(j_1 Int)) (and (<= 0 j_0) (<= j_0 (- NY 1)) (<= 1 i_0) (<= i_0 (- NX 1)) (<= 0 j_1) (<= j_1 (- NY 1)) (= i_0 0) (= j_0 j_1)))))
      (<= 0 t)
    )
    false
  )
))

(check-sat)