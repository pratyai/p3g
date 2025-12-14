(declare-fun _for_it_113 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_113 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_113)
  )
  (not (= _for_it_113 (+ _for_it_113 1)))
))

(check-sat)