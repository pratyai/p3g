(declare-fun _for_it_79 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_79 (+ _for_it_79 1)))
  (and
    (<= (+ kidia (- 1)) _for_it_79)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_79 1) (+ kfdia (- 1)))
  )
))

(check-sat)