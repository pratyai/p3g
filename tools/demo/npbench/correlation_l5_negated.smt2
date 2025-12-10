(declare-fun M () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and
  (or
    (not (= i (+ j 1)))
    (not (= j i))
  )
  (and
    (<= (+ i 1) j)
    (<= (+ j 1) (- M 1))
    (<= (+ i 2) (- M 1))
    (<= 1 (- M 2))
  )
  (not (= j (+ j 1)))
))

(check-sat)