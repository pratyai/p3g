(declare-fun _for_it_112 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_112 (+ _for_it_112 1)))
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_112 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_112)
    (<= kidia (+ kfdia (- 1)))
  )
))

(check-sat)