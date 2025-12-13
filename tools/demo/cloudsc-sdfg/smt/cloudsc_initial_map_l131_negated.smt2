(declare-fun _for_it_84 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_84 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_84)
    (<= kidia (+ kfdia (- 1)))
  )
  (not (= _for_it_84 (+ _for_it_84 1)))
))

(check-sat)