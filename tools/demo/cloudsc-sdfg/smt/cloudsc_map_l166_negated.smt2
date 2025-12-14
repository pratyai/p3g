(declare-fun _for_it_113 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_113 (+ _for_it_113 1)))
  (and
    (<= (+ kidia (- 1)) _for_it_113)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_113 1) (+ kfdia (- 1)))
  )
))

(check-sat)