

(assert (forall ((_for_it_96 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (exists ((_for_it_97_0 Int)(_for_it_98_1 Int)(_for_it_97_1 Int)) (and (<= _for_it_97_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_1) (<= _for_it_97_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_0) (<= 0 _for_it_98_1) (<= _for_it_98_1 4))) (exists ((_for_it_97_0 Int)(_for_it_98_0 Int)(_for_it_97_1 Int)) (and (<= 0 _for_it_98_0) (<= _for_it_98_0 4) (<= _for_it_97_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_1) (<= _for_it_97_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_0))) (exists ((_for_it_97_0 Int)(_for_it_98_0 Int)(_for_it_98_1 Int)(_for_it_97_1 Int)) (and (<= 0 _for_it_98_0) (<= _for_it_98_0 4) (<= _for_it_97_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_1) (<= _for_it_97_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_0) (<= 0 _for_it_98_1) (<= _for_it_98_1 4))) (exists ((_for_it_97_0 Int)(_for_it_97_1 Int)) (and (= _for_it_97_0 _for_it_97_1) (= _for_it_96 (+ _for_it_96 1)) (<= _for_it_97_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_1) (<= _for_it_97_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_0))) (exists ((_for_it_97_0 Int)(_for_it_97_1 Int)) (and (<= (+ kidia (- 1)) _for_it_97_1) (<= _for_it_97_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_97_0) (<= _for_it_97_1 (+ kfdia (- 1)))))))
      (<= 0 _for_it_96)
      (<= (+ _for_it_96 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)