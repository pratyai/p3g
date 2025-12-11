

(assert (forall ((N Int) (TSTEPS Int) (k Int))
  (=>
    (and
      (not (= k (+ k 1)))
      (<= 2 (+ N (- 2)))
      (<= 2 (+ TSTEPS (- 1)))
      (<= (+ k 1) (+ N (- 2)))
      (<= 1 k)
    )
    false
  )
))

(check-sat)