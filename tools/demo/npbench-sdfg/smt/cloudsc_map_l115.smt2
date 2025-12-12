

(assert (forall ((_for_it_68 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (= _for_it_68 (+ _for_it_68 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_68 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_68)
    )
    false
  )
))

(check-sat)