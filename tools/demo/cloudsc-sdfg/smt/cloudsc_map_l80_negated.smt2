(declare-fun _for_it_33 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_33 (+ _for_it_33 1)))
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_33 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_33)
  )
))

(check-sat)