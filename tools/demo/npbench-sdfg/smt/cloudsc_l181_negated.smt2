(declare-fun _for_it_128 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= 1 klev)
    (<= (+ _for_it_128 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_128)
    (<= kidia (+ kfdia (- 1)))
  )
  (not (= _for_it_128 (+ _for_it_128 1)))
))

(check-sat)