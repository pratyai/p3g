(declare-fun N () Int)
(declare-fun idx () Int)

(assert (and
  (and
    (<= 0 idx)
    (<= (+ idx 1) (- N 1))
    (<= 1 (- N 1))
  )
  (not (= idx (+ idx 1)))
))

(check-sat)