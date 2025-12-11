(declare-fun M () Int)
(declare-fun N () Int)
(declare-fun i_q () Int)

(assert (and
  (not (= i_q (+ i_q 1)))
  (and
    (<= 1 (+ N (- 1)))
    (<= 1 (+ M (- 1)))
    (<= 0 i_q)
    (<= (+ i_q 1) (+ M (- 1)))
  )
))

(check-sat)