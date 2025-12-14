(declare-fun _for_it_23 () Int)

(assert (forall ((_for_it_41 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_41 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_41)
      (not (or (< (+ _for_it_23 1) klev) (= _for_it_41 (+ _for_it_41 1)) (and (< (+ _for_it_23 1) klev) (= 0 (+ _for_it_41 1))) (and (< (+ _for_it_23 1) klev) (= _for_it_41 0))))
    )
    false
  )
))

(check-sat)