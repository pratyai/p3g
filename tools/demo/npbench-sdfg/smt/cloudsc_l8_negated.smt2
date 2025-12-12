(declare-fun _for_it_7 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (not (= _for_it_7 (+ _for_it_7 1)))
  (and
    (<= (+ _for_it_7 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_7)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
  )
))

(check-sat)