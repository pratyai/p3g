(declare-fun _for_it_116 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_116 (+ _for_it_116 1)))
  (and
    (<= (+ _for_it_116 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_116)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
  )
))

(check-sat)