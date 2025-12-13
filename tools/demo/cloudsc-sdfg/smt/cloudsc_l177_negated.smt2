(declare-fun _for_it_124 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)

(assert (and
  (and
    (<= (+ kidia (- 1)) _for_it_124)
    (<= kidia (+ kfdia (- 1)))
    (<= (+ _for_it_124 1) (+ kfdia (- 1)))
  )
  (not (= _for_it_124 (+ _for_it_124 1)))
))

(check-sat)