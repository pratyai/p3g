(declare-fun _for_it_109 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((_for_it_110_0 Int) (_for_it_110_1 Int))
    (or
      (not (<= _for_it_110_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_110_1))
      (not (<= _for_it_110_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_110_0))
      (not (= _for_it_110_0 _for_it_110_1))
      (not (= _for_it_109 (+ _for_it_109 1)))
    )
  )
  (and
    (<= (+ _for_it_109 1) 4)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 _for_it_109)
  )
))

(check-sat)