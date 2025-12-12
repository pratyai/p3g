

(assert (forall ((_for_it_125 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_125)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_125 1) (+ klev (- 1)))
      (not (or (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (= (+ _for_it_125 1) (+ _for_it_125 2)) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0) (= _for_it_126_0 _for_it_126_1))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (or (and (= (+ _for_it_125 1) (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1)) (= _for_it_126_0 _for_it_126_1)) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0) (= _for_it_126_0 _for_it_126_1))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (or (and (= (+ _for_it_125 1) (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1)) (and (= _for_it_125 (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1))) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (or (and (= (+ _for_it_125 1) (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1)) (= _for_it_126_0 _for_it_126_1) (and (= _for_it_125 (+ _for_it_125 2)) (= _for_it_126_0 _for_it_126_1))) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0))) (exists ((_for_it_126_1 Int)(_for_it_126_0 Int)) (and (= _for_it_125 (+ _for_it_125 2)) (<= _for_it_126_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_1) (<= _for_it_126_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_126_0) (= _for_it_126_0 _for_it_126_1)))))
    )
    false
  )
))

(check-sat)