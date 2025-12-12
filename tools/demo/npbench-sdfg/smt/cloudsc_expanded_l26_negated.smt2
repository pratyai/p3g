(declare-fun _for_it_14 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_14 1) (+ klev (- 1)))
    (<= 0 _for_it_14)
  )
  (forall ((_for_it_15_0 Int) (_for_it_15_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_15_0))
      (not (<= _for_it_15_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_15_1))
      (not (<= _for_it_15_0 (+ kfdia (- 1))))
    )
  )
))

(check-sat)