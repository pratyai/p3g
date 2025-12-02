(declare-fun M () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and
  (and
    (<= (+ j 1) (- M 1))
    (<= (+ i 2) (- M 1))
    (<= (+ i 1) j)
  )
  (or
    (not (= i (+ j 1)))
    (not (= j i))
  )
  (not (= j (+ j 1)))
))

(check-sat)