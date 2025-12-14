(declare-fun _for_it_1 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_1 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_1)
    (<= kidia (+ kfdia (- 1)))
  )
  (not (= _for_it_1 (+ _for_it_1 1)))
))

(check-sat)