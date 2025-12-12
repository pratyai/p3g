(declare-fun _for_it_10 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_10 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_10)
  )
  (not (= _for_it_10 (+ _for_it_10 1)))
))

(check-sat)