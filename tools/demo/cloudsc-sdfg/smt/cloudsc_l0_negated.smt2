(declare-fun _for_it_0 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (forall ((_for_it_1_0 Int) (_for_it_1_1 Int))
    (or
      (not (<= _for_it_1_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_1_0))
      (not (= _for_it_1_0 _for_it_1_1))
      (not (= _for_it_0 (+ _for_it_0 1)))
      (not (<= _for_it_1_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_1_1))
    )
  )
  (and
    (<= (+ _for_it_0 1) (+ klev (- 1)))
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_0)
    (<= 1 (+ klev (- 1)))
  )
))

(check-sat)