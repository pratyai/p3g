(declare-fun start_val () (Array Int Int))
(declare-fun stop_val () (Array Int Int))

(assert (forall ((M Int) (i Int))
  (=>
    (and
      (<= (+ i 1) (+ M (- 1)))
      (not (or (exists ((k_0 Int)) (and (<= k_0 (+ (select stop_val i) (- 1))) (<= (select start_val i) k_0) (= i (+ i 1)))) (= i (+ i 1)) (exists ((k_0 Int)(k_1 Int)) (and (= i (+ i 1)) (<= k_1 (+ (select stop_val (+ i 1)) (- 1))) (<= (select start_val (+ i 1)) k_1) (<= k_0 (+ (select stop_val i) (- 1))) (<= (select start_val i) k_0))) (exists ((k_1 Int)) (and (<= (select start_val (+ i 1)) k_1) (<= k_1 (+ (select stop_val (+ i 1)) (- 1))) (= i (+ i 1))))))
      (<= 0 i)
      (<= 1 (+ M (- 1)))
    )
    false
  )
))

(check-sat)