

(assert (forall ((M Int) (N Int) (i_q Int))
  (=>
    (and
      (not (= i_q (+ i_q 1)))
      (<= 1 (+ M (- 1)))
      (<= 1 (+ N (- 1)))
      (<= (+ i_q 1) (+ M (- 1)))
      (<= 0 i_q)
    )
    false
  )
))

(check-sat)