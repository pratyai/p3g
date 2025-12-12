

(assert (forall ((_for_it_107 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_107)
      (<= (+ _for_it_107 1) 3)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_108_0 Int)(_for_it_108_1 Int)) (and (<= _for_it_108_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_108_0) (<= _for_it_108_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_108_1))))
    )
    false
  )
))

(check-sat)