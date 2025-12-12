(declare-fun _for_it_3 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_3)
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_3 1) (+ klev (- 1)))
  )
  (forall ((_for_it_4_0 Int) (_for_it_4_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_4_1))
      (not (<= _for_it_4_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_4_0))
      (not (= _for_it_4_0 _for_it_4_1))
      (not (= _for_it_3 (+ _for_it_3 1)))
      (not (<= _for_it_4_1 (+ kfdia (- 1))))
    )
  )
))

(check-sat)