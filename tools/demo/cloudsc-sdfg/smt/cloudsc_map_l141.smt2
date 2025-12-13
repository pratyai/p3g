

(assert (forall ((_for_it_93 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (= _for_it_93 (+ _for_it_93 1)) (exists ((_for_it_94_1 Int)) (and (<= 0 _for_it_94_1) (<= _for_it_94_1 4) (= _for_it_93 (+ _for_it_93 1)))) (exists ((_for_it_94_0 Int)) (and (= _for_it_93 (+ _for_it_93 1)) (<= 0 _for_it_94_0) (<= _for_it_94_0 4))) (exists ((_for_it_94_0 Int)(_for_it_94_1 Int)) (and (= _for_it_93 (+ _for_it_93 1)) (<= 0 _for_it_94_1) (<= _for_it_94_1 4) (<= 0 _for_it_94_0) (<= _for_it_94_0 4)))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_93 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_93)
    )
    false
  )
))

(check-sat)