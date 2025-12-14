(declare-fun _for_it_76 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((_for_it_77_0 Int) (_for_it_77_1 Int))
    (or
      (not (<= (+ kidia (- 1)) _for_it_77_1))
      (not (<= _for_it_77_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_77_0))
      (not (= _for_it_77_0 _for_it_77_1))
      (not (= _for_it_76 (+ _for_it_76 1)))
      (not (<= _for_it_77_1 (+ kfdia (- 1))))
    )
  )
  (and
    (<= (+ _for_it_76 1) 4)
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_76)
    (<= ncldtop (+ klev (- 1)))
  )
))

(check-sat)