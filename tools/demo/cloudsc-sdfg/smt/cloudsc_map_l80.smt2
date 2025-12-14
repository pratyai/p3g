

(assert (forall ((_for_it_33 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (= _for_it_33 (+ _for_it_33 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_33 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_33)
    )
    false
  )
))

(check-sat)