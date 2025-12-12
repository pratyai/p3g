(declare-fun _for_it_122 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= 1 klev)
    (<= 0 _for_it_122)
    (<= (+ _for_it_122 1) klev)
    (<= kidia (+ kfdia (- 1)))
  )
  (forall ((_for_it_123_0 Int) (_for_it_123_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_123_1))
      (not (<= _for_it_123_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_123_0))
      (not (= _for_it_123_0 _for_it_123_1))
      (not (= _for_it_122 (+ _for_it_122 1)))
      (not (<= _for_it_123_1 (+ kfdia (- 1))))
    )
  )
))

(check-sat)