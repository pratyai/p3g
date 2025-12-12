

(assert (forall ((_for_it_7 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_7 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_7)
      (not (= _for_it_7 (+ _for_it_7 1)))
    )
    false
  )
))

(check-sat)