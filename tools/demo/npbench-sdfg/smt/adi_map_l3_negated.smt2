(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and
  (or
    (not (= i (+ i 1)))
    (not (= j (+ j (- 1))))
  )
  (not (= i (+ i 1)))
  (or
    (not (= (+ j (- 1)) j))
    (not (= i (+ i 1)))
  )
  (and
    (<= 2 TSTEPS)
    (<= (+ i 1) (+ N (- 2)))
    (<= 1 i)
    (<= 2 (+ N (- 2)))
  )
))

(check-sat)