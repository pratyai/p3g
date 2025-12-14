

(assert (forall ((_for_it_6 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (exists ((_for_it_7_0 Int)(_for_it_7_1 Int)) (and (<= _for_it_7_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_7_1) (<= _for_it_7_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_7_0) (= _for_it_7_0 _for_it_7_1) (= _for_it_6 (+ _for_it_6 1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_6 1) (+ klev (- 1)))
      (<= 0 _for_it_6)
    )
    false
  )
))

(check-sat)