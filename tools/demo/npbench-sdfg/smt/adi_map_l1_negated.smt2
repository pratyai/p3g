(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun i () Int)

(assert (and
  (and
    (<= 2 (+ N (- 2)))
    (<= 2 TSTEPS)
    (<= (+ i 1) (+ N (- 2)))
    (<= 1 i)
  )
  (not (= i (+ i 1)))
))

(check-sat)