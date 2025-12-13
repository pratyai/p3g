

(assert (forall ((_for_it_79 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ kidia (- 1)) _for_it_79)
      (not (= _for_it_79 (+ _for_it_79 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_79 1) (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)