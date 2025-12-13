(declare-fun _for_it_121 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= (+ kidia (- 1)) _for_it_121)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_121 1) (+ kfdia (- 1)))
  )
  (not (= _for_it_121 (+ _for_it_121 1)))
))

(check-sat)