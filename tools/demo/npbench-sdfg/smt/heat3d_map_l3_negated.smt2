(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun k () Int)

(assert (and
  (and
    (<= 2 (+ TSTEPS (- 1)))
    (<= (+ k 1) (+ N (- 2)))
    (<= 1 k)
    (<= 2 (+ N (- 2)))
  )
  (not (= k (+ k 1)))
))

(check-sat)