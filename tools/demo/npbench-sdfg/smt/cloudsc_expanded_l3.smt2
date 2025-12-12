

(assert (forall ((_for_it_3 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_3)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_3 1) (+ klev (- 1)))
      (not (exists ((_for_it_4_1 Int)(_for_it_4_0 Int)) (and (<= (+ kidia (- 1)) _for_it_4_1) (<= _for_it_4_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_4_0) (= _for_it_4_0 _for_it_4_1) (= _for_it_3 (+ _for_it_3 1)) (<= _for_it_4_1 (+ kfdia (- 1))))))
    )
    false
  )
))

(check-sat)