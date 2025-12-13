(declare-fun j () Int)

(assert (forall ((N Int) (TSTEPS Int) (i Int))
  (=>
    (and
      (<= 1 i)
      (not (or (and (= j (+ j (- 1))) (= i (+ i 1))) (and (= (+ j (- 1)) j) (= i (+ i 1))) (= i (+ i 1))))
      (<= 2 (+ N (- 2)))
      (<= 2 TSTEPS)
      (<= (+ i 1) (+ N (- 2)))
    )
    false
  )
))

(check-sat)