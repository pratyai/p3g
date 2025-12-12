(declare-fun _for_it_111 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= 0 _for_it_111)
    (<= kidia (+ kfdia (- 1)))
    (<= (+ _for_it_111 1) 4)
  )
  (forall ((_for_it_112_0 Int) (_for_it_112_1 Int))
    (or
      (not (<= _for_it_112_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_112_1))
      (not (<= _for_it_112_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_112_0))
      (not (= _for_it_112_0 _for_it_112_1))
      (not (= _for_it_111 (+ _for_it_111 1)))
    )
  )
))

(check-sat)