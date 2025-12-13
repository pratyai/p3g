

(assert (forall ((_for_it_127 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_127)
      (<= (+ _for_it_127 1) klev)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 klev)
      (not (exists ((_for_it_128_1 Int)(_for_it_128_0 Int)) (and (<= _for_it_128_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_128_1) (<= _for_it_128_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_128_0) (= _for_it_128_0 _for_it_128_1) (= _for_it_127 (+ _for_it_127 1)))))
    )
    false
  )
))

(check-sat)