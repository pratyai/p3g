(declare-fun N () Int)
(declare-fun i () Int)

(assert (and
  (not (= i (+ i 1)))
  (and
    (<= 0 i)
    (<= (+ i 1) (- N 1))
    (<= 1 (- N 1))
  )
  (or
    (not (<= 0 i))
    (not (<= i (- (+ i 1) 1)))
  )
  (or
    (not (<= 0 (+ i 1)))
    (not (<= (+ i 1) (- i 1)))
  )
))

(check-sat)