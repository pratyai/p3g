

(assert (forall ((N Int) (TSTEPS Int) (i Int))
  (=>
    (and
      (<= 2 (+ N (- 2)))
      (<= 2 TSTEPS)
      (<= 1 i)
      (<= (+ i 1) (+ N (- 2)))
      (not (= i (+ i 1)))
    )
    false
  )
))

(check-sat)