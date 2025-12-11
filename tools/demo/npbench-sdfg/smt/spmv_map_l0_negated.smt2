(declare-fun M () Int)
(declare-fun i () Int)
(declare-fun start () Int)
(declare-fun stop () Int)

(assert (and
  (forall ((k_1 Int))
    (or
      (not (<= start k_1))
      (not (<= k_1 (+ stop (- 1))))
      (not (= i (+ i 1)))
    )
  )
  (forall ((k_0 Int))
    (or
      (not (<= start k_0))
      (not (<= k_0 (+ stop (- 1))))
      (not (= i (+ i 1)))
    )
  )
  (not (= i (+ i 1)))
  (forall ((k_0 Int) (k_1 Int))
    (or
      (not (<= start k_1))
      (not (<= k_0 (+ stop (- 1))))
      (not (= i (+ i 1)))
      (not (<= start k_0))
      (not (<= k_1 (+ stop (- 1))))
    )
  )
  (and
    (<= 0 i)
    (<= 1 (+ M (- 1)))
    (<= (+ i 1) (+ M (- 1)))
    (<= (+ start 1) (+ stop (- 1)))
  )
))

(check-sat)