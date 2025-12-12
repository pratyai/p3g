(declare-fun _for_it_18 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (and
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_18 1) (+ klev (- 1)))
    (<= 0 _for_it_18)
    (<= kidia (+ kfdia (- 1)))
  )
  (forall ((_for_it_19_0 Int) (_for_it_19_1 Int))
    (or
      (not (<= _for_it_19_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_19_1))
      (not (<= _for_it_19_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_19_0))
      (not (= _for_it_19_0 _for_it_19_1))
      (not (= _for_it_18 (+ _for_it_18 1)))
    )
  )
  (forall ((_for_it_19_0 Int) (_for_it_19_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_19_1))
      (not (<= _for_it_19_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_19_0))
      (not (<= _for_it_19_1 (+ kfdia (- 1))))
    )
  )
))

(check-sat)