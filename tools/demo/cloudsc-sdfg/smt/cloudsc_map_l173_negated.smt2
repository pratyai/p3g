(declare-fun _for_it_120 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_120 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_120)
  )
  (not (= _for_it_120 (+ _for_it_120 1)))
))

(check-sat)