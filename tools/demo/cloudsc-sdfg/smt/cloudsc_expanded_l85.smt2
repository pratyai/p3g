(declare-fun _for_it_23 () Int)

(assert (forall ((_for_it_38 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_38 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_38)
      (not (or (< (+ _for_it_23 1) klev) (and (< (+ _for_it_23 1) klev) (= _for_it_38 (+ _for_it_38 1)))))
    )
    false
  )
))

(check-sat)