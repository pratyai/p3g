(declare-fun j () Int)

(assert (forall ((N Int) (TSTEPS Int) (i Int))
  (=>
    (and
      (<= 1 i)
      (not (or (= i (+ i 1)) (and (= j (+ j (- 1))) (= i (+ i 1))) (and (= i (+ i 1)) (= (+ j (- 1)) j))))
      (<= 2 (+ N (- 2)))
      (<= 2 TSTEPS)
      (<= (+ i 1) (+ N (- 2)))
    )
    false
  )
))

(check-sat)