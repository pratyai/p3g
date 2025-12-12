

(assert (forall ((_for_it_80 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_80)
      (<= (+ _for_it_80 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0))))
    )
    false
  )
))

(check-sat)