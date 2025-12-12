(declare-fun _for_it_38 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (<= ncldtop (+ klev (- 1)))
  (<= (+ _for_it_38 1) (+ kfdia (- 1)))
  (<= (+ kidia (- 1)) _for_it_38)
  (<= kidia (+ kfdia (- 1)))
))

(check-sat)