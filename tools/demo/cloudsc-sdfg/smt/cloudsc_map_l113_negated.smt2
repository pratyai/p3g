(declare-fun _for_it_66 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= (+ _for_it_66 1) 4)
    (<= ncldtop (+ klev (- 1)))
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_66)
  )
  (forall ((_for_it_67_0 Int) (_for_it_67_1 Int))
    (or
      (not (<= _for_it_67_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_67_1))
      (not (<= _for_it_67_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_67_0))
      (not (= _for_it_67_0 _for_it_67_1))
      (not (= _for_it_66 (+ _for_it_66 1)))
    )
  )
))

(check-sat)