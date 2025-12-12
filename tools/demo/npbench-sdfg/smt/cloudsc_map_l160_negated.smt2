(declare-fun _for_it_107 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= (+ _for_it_107 1) 3)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 _for_it_107)
  )
  (forall ((_for_it_108_0 Int) (_for_it_108_1 Int))
    (or
      (not (<= _for_it_108_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_108_0))
      (not (<= _for_it_108_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_108_1))
    )
  )
))

(check-sat)