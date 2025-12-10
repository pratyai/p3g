

(assert (forall ((M Int) (N Int) (i Int) (j Int))
  (=>
    (and
      (<= (+ i 1) j)
      (<= (+ j 1) (- M 1))
      (<= (+ i 2) (- M 1))
      (<= 1 (- M 2))
      (not (or (and (= i (+ j 1)) (= j i)) (= j (+ j 1))))
    )
    false
  )
))

(check-sat)