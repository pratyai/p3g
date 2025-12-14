(declare-fun _for_it_123 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (not (= _for_it_123 (+ _for_it_123 1)))
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= 1 klev)
    (<= (+ _for_it_123 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_123)
  )
))

(check-sat)