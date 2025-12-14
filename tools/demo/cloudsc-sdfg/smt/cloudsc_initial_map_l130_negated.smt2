(declare-fun _for_it_83 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((_for_it_84_0 Int) (_for_it_84_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_84_1))
      (not (<= _for_it_84_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_84_0))
      (not (= _for_it_84_0 _for_it_84_1))
      (not (= _for_it_83 (+ _for_it_83 1)))
      (not (<= _for_it_84_1 (+ kfdia (- 1))))
    )
  )
  (and
    (<= (+ _for_it_83 1) 4)
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_83)
    (<= ncldtop (+ klev (- 1)))
  )
))

(check-sat)