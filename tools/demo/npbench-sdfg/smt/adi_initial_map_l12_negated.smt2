(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and
  (or
    (not (= i (+ i 1)))
    (not (= j (+ j 1)))
  )
  (or
    (not (= i (+ i 1)))
    (not (= (+ j 1) j))
  )
  (and
    (<= 1 i)
    (<= 2 (+ N (- 2)))
    (<= (+ N (- 1)) 1)
    (<= 2 TSTEPS)
    (<= (+ i 1) (+ N (- 2)))
  )
  (not (= i (+ i 1)))
))

(check-sat)