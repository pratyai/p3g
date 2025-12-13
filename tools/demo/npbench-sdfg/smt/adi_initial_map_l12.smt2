(declare-fun j () Int)

(assert (forall ((N Int) (TSTEPS Int) (i Int))
  (=>
    (and
      (not (or (and (= i (+ i 1)) (= j (+ j 1))) (and (= i (+ i 1)) (= (+ j 1) j)) (= i (+ i 1))))
      (<= 1 i)
      (<= 2 (+ N (- 2)))
      (<= (+ N (- 1)) 1)
      (<= 2 TSTEPS)
      (<= (+ i 1) (+ N (- 2)))
    )
    false
  )
))

(check-sat)