(declare-fun _for_it_23 () Int)
(declare-fun _for_it_38 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_38 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_38)
  )
  (or
    (not (< (+ _for_it_23 1) klev))
    (not (= _for_it_38 (+ _for_it_38 1)))
  )
  (not (< (+ _for_it_23 1) klev))
))

(check-sat)