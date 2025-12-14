

(assert (forall ((_for_it_9 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_9)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_9 1) (+ klev (- 1)))
      (not (exists ((_for_it_10_0 Int)(_for_it_10_1 Int)) (and (<= _for_it_10_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_10_1) (<= _for_it_10_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_10_0) (= _for_it_10_0 _for_it_10_1) (= _for_it_9 (+ _for_it_9 1)))))
    )
    false
  )
))

(check-sat)