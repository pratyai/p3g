(declare-fun A_row_val () (Array Int Int))

(assert (forall ((M Int) (i Int))
  (=>
    (and
      (<= (+ i 1) (- M 1))
      (not (or (exists ((k_0 Int)) (and (= i (+ i 1)) (<= k_0 (- (select A_row_val (+ i 1)) 1)) (<= (select A_row_val i) k_0))) (= i (+ i 1)) (exists ((k_0 Int)(k_1 Int)) (and (<= k_1 (- (select A_row_val (+ i 2)) 1)) (= i (+ i 1)) (<= (select A_row_val (+ i 1)) k_1) (<= k_0 (- (select A_row_val (+ i 1)) 1)) (<= (select A_row_val i) k_0))) (exists ((k_1 Int)) (and (<= k_1 (- (select A_row_val (+ i 2)) 1)) (= i (+ i 1)) (<= (select A_row_val (+ i 1)) k_1)))))
      (<= 1 (- M 1))
      (<= 0 i)
    )
    false
  )
))

(check-sat)