(declare-fun _for_it_128 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (not (= _for_it_128 (+ _for_it_128 1)))
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= 1 klev)
    (<= (+ _for_it_128 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_128)
  )
))

(check-sat)