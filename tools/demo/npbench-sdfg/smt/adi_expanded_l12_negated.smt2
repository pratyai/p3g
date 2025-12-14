(declare-fun N () Int)
(declare-fun TSTEPS () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and
  (not (= i (+ i 1)))
  (or
    (not (= (- (+ N (- 2)) j) (- (+ N (- 1)) j)))
    (not (= i (+ i 1)))
  )
  (and
    (<= 1 i)
    (<= 2 (+ N (- 2)))
    (<= 2 TSTEPS)
    (<= (+ i 1) (+ N (- 2)))
  )
  (or
    (not (= i (+ i 1)))
    (not (= (- (+ N (- 1)) j) (- (+ N (- 2)) j)))
  )
))

(check-sat)