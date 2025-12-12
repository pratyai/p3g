

(assert (forall ((_for_it_11 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_11)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_11 1) (+ klev (- 1)))
      (not (exists ((_for_it_12_1 Int)(_for_it_12_0 Int)) (and (<= (+ kidia (- 1)) _for_it_12_1) (<= _for_it_12_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_0) (<= _for_it_12_1 (+ kfdia (- 1))))))
    )
    false
  )
))

(check-sat)