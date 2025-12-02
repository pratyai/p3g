

(assert (forall ((M Int) (N Int) (i Int) (j Int))
  (=>
    (and
      (<= (+ j 1) (- M 1))
      (not (or (and (= i (+ j 1)) (= j i)) (= j (+ j 1))))
      (<= (+ i 2) (- M 1))
      (<= (+ i 1) j)
    )
    false
  )
))

(check-sat)