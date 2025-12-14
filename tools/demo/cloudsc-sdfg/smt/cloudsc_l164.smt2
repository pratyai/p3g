

(assert (forall ((_for_it_111 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_111)
      (<= (+ _for_it_111 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_112_1 Int)(_for_it_112_0 Int)) (and (<= _for_it_112_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_112_0) (= _for_it_112_0 _for_it_112_1) (= _for_it_111 (+ _for_it_111 1)) (<= _for_it_112_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_112_1))))
    )
    false
  )
))

(check-sat)