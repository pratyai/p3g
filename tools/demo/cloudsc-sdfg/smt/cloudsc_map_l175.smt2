

(assert (forall ((_for_it_122 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_122)
      (<= (+ _for_it_122 1) klev)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 klev)
      (not (exists ((_for_it_123_1 Int)(_for_it_123_0 Int)) (and (<= _for_it_123_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_123_1) (<= _for_it_123_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_123_0) (= _for_it_123_0 _for_it_123_1) (= _for_it_122 (+ _for_it_122 1)))))
    )
    false
  )
))

(check-sat)