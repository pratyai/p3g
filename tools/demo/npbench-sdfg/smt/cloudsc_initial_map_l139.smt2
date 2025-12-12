

(assert (forall ((_for_it_91 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= 0 _for_it_91)
      (<= (+ _for_it_91 1) 4)
      (not (exists ((_for_it_95_0 Int)(_for_it_92_0 Int)(_for_it_92_1 Int)(_for_it_95_1 Int)) (and (<= 0 _for_it_92_0) (<= _for_it_95_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_95_0) (<= _for_it_92_0 4) (<= 0 _for_it_92_1) (<= _for_it_92_1 4) (= _for_it_95_0 _for_it_95_1) (<= _for_it_95_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_95_1) (= _for_it_92_0 _for_it_92_1) (= _for_it_91 (+ _for_it_91 1)))))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)