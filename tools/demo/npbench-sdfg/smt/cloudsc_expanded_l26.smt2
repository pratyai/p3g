

(assert (forall ((_for_it_14 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (exists ((_for_it_15_0 Int)(_for_it_15_1 Int)) (and (<= (+ kidia (- 1)) _for_it_15_0) (<= _for_it_15_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_15_1) (<= _for_it_15_0 (+ kfdia (- 1))))))
      (<= 0 _for_it_14)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_14 1) (+ klev (- 1)))
    )
    false
  )
))

(check-sat)