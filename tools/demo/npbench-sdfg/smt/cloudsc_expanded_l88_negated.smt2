(declare-fun _for_it_41 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_41 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_41)
  )
  (not (= _for_it_41 (+ _for_it_41 1)))
))

(check-sat)