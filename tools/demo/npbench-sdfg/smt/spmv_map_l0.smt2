

(assert (forall ((M Int) (i Int) (start Int) (stop Int))
  (=>
    (and
      (<= 0 i)
      (not (or (exists ((k_1 Int)) (and (<= start k_1) (<= k_1 (+ stop (- 1))) (= i (+ i 1)))) (exists ((k_0 Int)) (and (<= start k_0) (= i (+ i 1)) (<= k_0 (+ stop (- 1))))) (exists ((k_0 Int)(k_1 Int)) (and (<= start k_1) (<= k_0 (+ stop (- 1))) (= i (+ i 1)) (<= start k_0) (<= k_1 (+ stop (- 1))))) (= i (+ i 1))))
      (<= (+ start 1) (+ stop (- 1)))
      (<= 1 (+ M (- 1)))
      (<= (+ i 1) (+ M (- 1)))
    )
    false
  )
))

(check-sat)