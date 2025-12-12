

(assert (forall ((_for_it_78 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (exists ((_for_it_82_0 Int)(_for_it_82_1 Int)) (and (<= _for_it_82_0 (+ kfdia (- 1))) (<= _for_it_82_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_82_1) (= _for_it_82_0 _for_it_82_1) (<= (+ kidia (- 1)) _for_it_82_0))) (exists ((_for_it_79_0 Int)(_for_it_79_1 Int)) (and (<= _for_it_79_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_79_1) (<= _for_it_79_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_79_0) (= _for_it_79_0 _for_it_79_1))) (exists ((_for_it_82_0 Int)(_for_it_82_1 Int)) (and (<= (+ kidia (- 1)) _for_it_82_1) (<= _for_it_82_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_82_0) (<= _for_it_82_1 (+ kfdia (- 1))))) (exists ((_for_it_81_1 Int)(_for_it_81_0 Int)(_for_it_80_1 Int)(_for_it_80_0 Int)) (and (<= 0 _for_it_80_0) (<= _for_it_80_0 4) (<= (+ kidia (- 1)) _for_it_81_0) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= 0 _for_it_80_1) (<= _for_it_80_1 4) (<= _for_it_81_1 (+ kfdia (- 1)))))))
      (<= 0 _for_it_78)
      (<= (+ _for_it_78 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)