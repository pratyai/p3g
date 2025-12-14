

(assert (forall ((_for_it_72 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= 0 _for_it_72)
      (<= (+ _for_it_72 1) 4)
      (not (or (exists ((_for_it_73_0 Int)(_for_it_73_1 Int)) (and (<= _for_it_73_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_73_1) (<= _for_it_73_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_73_0))) (exists ((_for_it_73_0 Int)(_for_it_73_1 Int)) (and (<= _for_it_73_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_73_1) (<= _for_it_73_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_73_0) (= _for_it_73_0 _for_it_73_1) (= _for_it_72 (+ _for_it_72 1))))))
    )
    false
  )
))

(check-sat)