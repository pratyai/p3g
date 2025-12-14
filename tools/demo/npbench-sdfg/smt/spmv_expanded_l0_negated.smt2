(declare-fun M () Int)
(declare-fun i () Int)

(assert (forall ((start_val (Array Int Int)) (stop_val (Array Int Int)))
  (and
    (not (= i (+ i 1)))
    (forall ((k_1 Int))
      (or
        (not (<= (select start_val (+ i 1)) k_1))
        (not (<= k_1 (+ (select stop_val (+ i 1)) (- 1))))
        (not (= i (+ i 1)))
      )
    )
    (forall ((k_0 Int))
      (or
        (not (<= k_0 (+ (select stop_val i) (- 1))))
        (not (<= (select start_val i) k_0))
        (not (= i (+ i 1)))
      )
    )
    (and
      (<= (+ i 1) (+ M (- 1)))
      (<= 0 i)
      (<= 1 (+ M (- 1)))
    )
    (forall ((k_0 Int) (k_1 Int))
      (or
        (not (= i (+ i 1)))
        (not (<= k_1 (+ (select stop_val (+ i 1)) (- 1))))
        (not (<= (select start_val (+ i 1)) k_1))
        (not (<= k_0 (+ (select stop_val i) (- 1))))
        (not (<= (select start_val i) k_0))
      )
    )
  )
))

(check-sat)