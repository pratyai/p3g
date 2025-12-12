(declare-fun _for_it_11 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= (+ _for_it_11 1) (+ klev (- 1)))
    (<= 0 _for_it_11)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
  )
  (forall ((_for_it_12_0 Int) (_for_it_12_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_12_1))
      (not (<= _for_it_12_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_12_0))
      (not (<= _for_it_12_1 (+ kfdia (- 1))))
    )
  )
))

(check-sat)