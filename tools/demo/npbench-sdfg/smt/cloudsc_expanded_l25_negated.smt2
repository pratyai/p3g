(declare-fun _for_it_13 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (forall ((_for_it_14_0 Int) (_for_it_14_1 Int) (_for_it_15_0 Int) (_for_it_15_1 Int))
    (or
      (not (<= _for_it_15_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_15_1))
      (not (<= _for_it_14_1 (+ klev (- 1))))
      (not (<= 0 _for_it_14_0))
      (not (<= _for_it_15_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_15_0))
      (not (<= _for_it_14_0 (+ klev (- 1))))
      (not (<= 0 _for_it_14_1))
    )
  )
  (and
    (<= (+ _for_it_13 1) 3)
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_13)
    (<= 1 (+ klev (- 1)))
  )
))

(check-sat)