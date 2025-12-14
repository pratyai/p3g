

(assert (forall ((_for_it_125 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 0 _for_it_125)
      (<= (+ _for_it_125 1) (+ klev (- 1)))
      (<= 1 (+ klev (- 1)))
      (not (or (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (= _for_it_126_0 _for_it_126_1) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0) (= (+ _for_it_125 1) (+ _for_it_125 2)))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0) (<= _for_it_126_1 (+ kfdia (- 1))))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (= (- (+ (* _for_it_125 (- kfdia kidia)) _for_it_126_0 1) kidia) (- (+ (* (+ _for_it_125 1) (- kfdia kidia)) _for_it_126_1 1) kidia)) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (or (and (= _for_it_126_0 _for_it_126_1) (= (+ _for_it_125 1) (+ _for_it_125 2))) (= _for_it_126_0 _for_it_126_1)) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (= _for_it_126_0 _for_it_126_1) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (or (and (= _for_it_126_0 _for_it_126_1) (= (+ _for_it_125 1) (+ _for_it_125 2))) (and (= _for_it_125 (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1))) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (<= _for_it_126_1 (+ kfdia (- 1))) (or (and (= _for_it_126_0 _for_it_126_1) (= (+ _for_it_125 1) (+ _for_it_125 2))) (and (= _for_it_125 (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1)) (= _for_it_126_0 _for_it_126_1)) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (= _for_it_125 (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0)))))
    )
    false
  )
))

(check-sat)