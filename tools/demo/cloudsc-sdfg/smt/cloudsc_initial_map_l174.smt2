

(assert (forall ((_for_it_121 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ kidia (- 1)) _for_it_121)
      (not (= _for_it_121 (+ _for_it_121 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_121 1) (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)