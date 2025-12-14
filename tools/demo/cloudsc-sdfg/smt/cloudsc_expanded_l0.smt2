

(assert (forall ((_for_it_0 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_0 1) (+ klev (- 1)))
      (not (exists ((_for_it_1_0 Int)(_for_it_1_1 Int)) (and (<= _for_it_1_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_1_0) (= _for_it_1_0 _for_it_1_1) (= _for_it_0 (+ _for_it_0 1)) (<= _for_it_1_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_1_1))))
      (<= 0 _for_it_0)
    )
    false
  )
))

(check-sat)