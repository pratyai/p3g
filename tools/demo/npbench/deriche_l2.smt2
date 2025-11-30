(declare-fun W () Int)

(assert (forall ((H Int) (j Int))
  (=>
    (and
      (<= 2 j)
      (<= 3 (- H 1))
      (not (exists ((i_1 Int)(i_0 Int)) (and (<= 0 i_0) (<= i_0 (- W 1)) (<= 0 i_1) (<= i_1 (- W 1)) (or (and (= i_0 i_1) (= (- j 2) (+ j 1))) (and (= i_0 i_1) (= j (- (+ j 1) 1))) (and (= i_0 i_1) (= j (- (+ j 1) 2))) (and (= i_0 i_1) (= j (+ j 1))) (and (= i_0 i_1) (= (- j 1) (+ j 1)))))))
      (<= (+ j 1) (- H 1))
    )
    false
  )
))

(check-sat)