(declare-fun N () Int)
(declare-fun i () Int)

(assert (forall ((bin_idx_u_val (Array Int Int)))
  (and
    (not (= (select bin_idx_u_val i) (select bin_idx_u_val (+ i 1))))
    (and
      (<= 0 i)
      (<= (+ i 1) (- N 1))
      (<= 1 (- N 1))
    )
    (not (= i (+ i 1)))
  )
))

(check-sat)