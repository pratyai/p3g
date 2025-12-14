

(assert (forall ((_for_it_8 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ _for_it_8 1) 3)
      (not (exists ((_for_it_9_0 Int)(_for_it_9_1 Int)(_for_it_10_0 Int)(_for_it_10_1 Int)) (and (<= _for_it_10_1 (+ kfdia (- 1))) (<= 0 _for_it_9_0) (<= (+ kidia (- 1)) _for_it_10_1) (<= _for_it_9_1 (+ klev (- 1))) (<= 0 _for_it_9_1) (<= _for_it_10_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_10_0) (<= _for_it_9_0 (+ klev (- 1))) (= _for_it_10_0 _for_it_10_1) (= _for_it_9_0 _for_it_9_1) (= _for_it_8 (+ _for_it_8 1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= 0 _for_it_8)
    )
    false
  )
))

(check-sat)