

(assert (forall ((_for_it_25 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_25 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_25)
      (not (= _for_it_25 (+ _for_it_25 1)))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)