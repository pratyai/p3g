

(assert (forall ((_for_it_83 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_83)
      (<= (+ _for_it_83 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_84_0 Int)(_for_it_84_1 Int)) (and (<= (+ kidia (- 1)) _for_it_84_1) (<= _for_it_84_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_84_0) (= _for_it_84_0 _for_it_84_1) (= _for_it_83 (+ _for_it_83 1)) (<= _for_it_84_1 (+ kfdia (- 1))))))
    )
    false
  )
))

(check-sat)