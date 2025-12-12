

(assert (forall ((_for_it_92 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (exists ((_for_it_95_0 Int)(_for_it_95_1 Int)) (and (<= _for_it_95_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_95_0) (<= _for_it_95_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_95_1) (= _for_it_95_0 _for_it_95_1) (= _for_it_92 (+ _for_it_92 1)))))
      (<= 0 _for_it_92)
      (<= (+ _for_it_92 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)