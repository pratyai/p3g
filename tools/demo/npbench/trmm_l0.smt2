(declare-fun N () Int)

(assert (forall ((M Int) (i Int))
  (=>
    (and
      (<= 0 i)
      (not (exists ((j_1 Int)(j_0 Int)) (and (or (and (= j_0 j_1) (<= (+ i 2) i) (<= i (- M 1))) (and (= i (+ i 1)) (= j_0 j_1)) (and (= j_0 j_1) (<= (+ i 1) (+ i 1)) (<= (+ i 1) (- M 1)))) (<= 0 j_0) (<= j_0 (- N 1)) (<= 0 j_1) (<= j_1 (- N 1)))))
      (<= 1 (- M 1))
      (<= (+ i 1) (- M 1))
    )
    false
  )
))

(check-sat)