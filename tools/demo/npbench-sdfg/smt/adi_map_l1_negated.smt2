(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun i () Int)

(assert (and
  (not (= i (+ i 1)))
  (and
    (<= 2 (+ N (- 2)))
    (<= 2 TSTEPS)
    (<= 1 i)
    (<= (+ i 1) (+ N (- 2)))
  )
))

(check-sat)