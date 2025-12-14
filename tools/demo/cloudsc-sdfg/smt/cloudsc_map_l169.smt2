

(assert (forall ((_for_it_116 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (= _for_it_116 (+ _for_it_116 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_116 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_116)
    )
    false
  )
))

(check-sat)