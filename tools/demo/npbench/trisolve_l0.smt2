

(assert (forall ((N Int) (i Int))
  (=>
    (and
      (<= 0 i)
      (<= (+ i 1) (- N 1))
      (not (or (= i (+ i 1)) (and (<= 0 i) (<= i (- (+ i 1) 1))) (and (<= 0 (+ i 1)) (<= (+ i 1) (- i 1)))))
      (<= 1 (- N 1))
    )
    false
  )
))

(check-sat)