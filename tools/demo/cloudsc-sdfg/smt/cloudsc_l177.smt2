

(assert (forall ((_for_it_124 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ kidia (- 1)) _for_it_124)
      (not (= _for_it_124 (+ _for_it_124 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= (+ _for_it_124 1) (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)