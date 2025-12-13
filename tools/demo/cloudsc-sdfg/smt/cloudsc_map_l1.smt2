

(assert (forall ((_for_it_1 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_1 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_1)
      (not (= _for_it_1 (+ _for_it_1 1)))
    )
    false
  )
))

(check-sat)