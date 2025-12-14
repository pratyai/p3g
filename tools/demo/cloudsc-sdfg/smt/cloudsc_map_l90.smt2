

(assert (forall ((_for_it_43 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_43 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_43)
      (not (= _for_it_43 (+ _for_it_43 1)))
    )
    false
  )
))

(check-sat)