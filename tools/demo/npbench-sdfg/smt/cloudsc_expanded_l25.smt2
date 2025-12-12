

(assert (forall ((_for_it_13 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_13)
      (<= (+ _for_it_13 1) 3)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (not (exists ((_for_it_14_0 Int)(_for_it_14_1 Int)(_for_it_15_0 Int)(_for_it_15_1 Int)) (and (<= _for_it_15_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_15_1) (<= _for_it_14_1 (+ klev (- 1))) (<= 0 _for_it_14_0) (<= _for_it_15_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_15_0) (<= _for_it_14_0 (+ klev (- 1))) (<= 0 _for_it_14_1))))
    )
    false
  )
))

(check-sat)