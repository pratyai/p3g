

(assert (forall ((_for_it_24 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_24)
      (<= (+ _for_it_24 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_25_0 Int)(_for_it_25_1 Int)) (and (<= (+ kidia (- 1)) _for_it_25_1) (<= _for_it_25_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_25_0) (= _for_it_25_0 _for_it_25_1) (= _for_it_24 (+ _for_it_24 1)) (<= _for_it_25_1 (+ kfdia (- 1))))))
    )
    false
  )
))

(check-sat)