(declare-fun M () Int)
(declare-fun N () Int)
(declare-fun i_sub () Int)

(assert (and
  (not (= i_sub (+ i_sub 1)))
  (and
    (<= 0 i_sub)
    (<= (+ i_sub 1) (+ M (- 1)))
    (<= 1 (+ N (- 1)))
    (<= 1 (+ M (- 1)))
  )
))

(check-sat)