

(assert (forall ((M Int) (N Int) (i_sub Int))
  (=>
    (and
      (<= 0 i_sub)
      (not (= i_sub (+ i_sub 1)))
      (<= 1 (+ M (- 1)))
      (<= 1 (+ N (- 1)))
      (<= (+ i_sub 1) (+ M (- 1)))
    )
    false
  )
))

(check-sat)