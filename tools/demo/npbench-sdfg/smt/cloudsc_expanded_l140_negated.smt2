(declare-fun _for_it_92 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= (+ _for_it_92 1) 4)
    (<= ncldtop (+ klev (- 1)))
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_92)
  )
  (forall ((_for_it_95_0 Int) (_for_it_95_1 Int))
    (or
      (not (<= _for_it_95_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_95_0))
      (not (= _for_it_95_0 _for_it_95_1))
      (not (<= (+ kidia (- 1)) _for_it_95_1))
      (not (<= _for_it_95_1 (+ kfdia (- 1))))
      (not (= _for_it_92 (+ _for_it_92 1)))
    )
  )
))

(check-sat)