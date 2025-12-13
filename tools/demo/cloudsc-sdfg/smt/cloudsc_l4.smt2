

(assert (forall ((_for_it_4 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ _for_it_4 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_4)
      (not (= _for_it_4 (+ _for_it_4 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
    )
    false
  )
))

(check-sat)