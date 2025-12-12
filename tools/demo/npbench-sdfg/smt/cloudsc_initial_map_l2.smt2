

(assert (forall ((_for_it_2 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_2)
      (not (exists ((_for_it_3_1 Int)(_for_it_4_0 Int)(_for_it_4_1 Int)(_for_it_3_0 Int)) (and (<= _for_it_4_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_4_1) (<= 0 _for_it_3_0) (<= _for_it_3_1 (+ klev (- 1))) (<= 0 _for_it_3_1) (<= (+ kidia (- 1)) _for_it_4_0) (<= _for_it_4_0 (+ kfdia (- 1))) (<= _for_it_3_0 (+ klev (- 1))) (= _for_it_4_0 _for_it_4_1) (= _for_it_3_0 _for_it_3_1) (= _for_it_2 (+ _for_it_2 1)))))
      (<= (+ _for_it_2 1) 3)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
    )
    false
  )
))

(check-sat)