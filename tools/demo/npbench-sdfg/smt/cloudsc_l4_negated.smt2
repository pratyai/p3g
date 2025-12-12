(declare-fun _for_it_4 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= (+ kidia (- 1)) _for_it_4)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_4 1) (+ kfdia (- 1)))
  )
  (not (= _for_it_4 (+ _for_it_4 1)))
))

(check-sat)