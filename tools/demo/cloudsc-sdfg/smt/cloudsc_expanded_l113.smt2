

(assert (forall ((_for_it_66 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_66)
      (<= (+ _for_it_66 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_67_1 Int)(_for_it_67_0 Int)) (and (<= _for_it_67_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_67_0) (= _for_it_67_0 _for_it_67_1) (= _for_it_66 (+ _for_it_66 1)) (<= _for_it_67_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_67_1))))
    )
    false
  )
))

(check-sat)