(declare-fun _for_it_4 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (not (= _for_it_4 (+ _for_it_4 1)))
  (and
    (<= (+ _for_it_4 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_4)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
  )
))

(check-sat)