(declare-fun _for_it_127 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= (+ _for_it_127 1) klev)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 klev)
    (<= 0 _for_it_127)
  )
  (forall ((_for_it_128_0 Int) (_for_it_128_1 Int))
    (or
      (not (= _for_it_128_0 _for_it_128_1))
      (not (= _for_it_127 (+ _for_it_127 1)))
      (not (<= _for_it_128_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_128_1))
      (not (<= _for_it_128_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_128_0))
    )
  )
))

(check-sat)