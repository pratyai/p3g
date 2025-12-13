

(assert (forall ((N Int) (TSTEPS Int) (i Int))
  (=>
    (and
      (<= 1 i)
      (not (= i (+ i 1)))
      (<= 2 (+ N (- 2)))
      (<= 2 TSTEPS)
      (<= (+ i 1) (+ N (- 2)))
    )
    false
  )
))

(check-sat)