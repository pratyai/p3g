(declare-fun _for_it_72 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= 0 _for_it_72)
    (<= (+ _for_it_72 1) 4)
    (<= ncldtop (+ klev (- 1)))
    (<= kidia (+ kfdia (- 1)))
  )
  (forall ((_for_it_73_0 Int) (_for_it_73_1 Int))
    (or
      (not (<= _for_it_73_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_73_0))
      (not (= _for_it_73_0 _for_it_73_1))
      (not (= _for_it_72 (+ _for_it_72 1)))
      (not (<= _for_it_73_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_73_1))
    )
  )
  (forall ((_for_it_73_0 Int) (_for_it_73_1 Int))
    (or
      (not (<= _for_it_73_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_73_0))
      (not (<= _for_it_73_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_73_1))
    )
  )
))

(check-sat)