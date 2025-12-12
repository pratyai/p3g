(declare-fun _for_it_74 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((_for_it_75_0 Int) (_for_it_75_1 Int))
    (or
      (not (<= _for_it_75_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_75_0))
      (not (= _for_it_75_0 _for_it_75_1))
      (not (= _for_it_74 (+ _for_it_74 1)))
      (not (<= _for_it_75_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_75_1))
    )
  )
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_74)
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_74 1) 4)
  )
))

(check-sat)