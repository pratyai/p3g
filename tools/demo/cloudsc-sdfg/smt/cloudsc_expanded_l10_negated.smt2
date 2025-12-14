(declare-fun _for_it_9 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (forall ((_for_it_10_0 Int) (_for_it_10_1 Int))
    (or
      (not (<= _for_it_10_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_10_0))
      (not (= _for_it_10_0 _for_it_10_1))
      (not (= _for_it_9 (+ _for_it_9 1)))
      (not (<= _for_it_10_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_10_1))
    )
  )
  (and
    (<= (+ _for_it_9 1) (+ klev (- 1)))
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= 0 _for_it_9)
  )
))

(check-sat)