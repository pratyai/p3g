(declare-fun bin_idx_u_val () (Array Int Int))

(assert (forall ((N Int) (i Int) (npt Int))
  (=>
    (and
      (<= 0 i)
      (not (or (= (select bin_idx_u_val i) (select bin_idx_u_val (+ i 1))) (= i (+ i 1))))
      (<= (+ i 1) (- N 1))
      (<= 1 (- N 1))
    )
    false
  )
))

(check-sat)