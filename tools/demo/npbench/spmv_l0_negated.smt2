(declare-fun M () Int)
(declare-fun i () Int)

(assert (forall ((A_row_val (Array Int Int)))
  (and
    (not (= i (+ i 1)))
    (forall ((k_0 Int))
      (or
        (not (<= k_0 (- (select A_row_val (+ i 1)) 1)))
        (not (= i (+ i 1)))
        (not (<= (select A_row_val i) k_0))
      )
    )
    (forall ((k_1 Int))
      (or
        (not (<= k_1 (- (select A_row_val (+ i 2)) 1)))
        (not (= i (+ i 1)))
        (not (<= (select A_row_val (+ i 1)) k_1))
      )
    )
    (and
      (<= (+ i 1) (- M 1))
      (<= 1 (- M 1))
      (<= 0 i)
    )
    (forall ((k_0 Int) (k_1 Int))
      (or
        (not (<= k_1 (- (select A_row_val (+ i 2)) 1)))
        (not (= i (+ i 1)))
        (not (<= (select A_row_val (+ i 1)) k_1))
        (not (<= k_0 (- (select A_row_val (+ i 1)) 1)))
        (not (<= (select A_row_val i) k_0))
      )
    )
  )
))

(check-sat)