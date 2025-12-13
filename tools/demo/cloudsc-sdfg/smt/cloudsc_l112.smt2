

(assert (forall ((_for_it_65 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= 0 _for_it_65)
      (<= (+ _for_it_65 1) 4)
      (not (or (exists ((_for_it_66_0 Int)(_for_it_66_1 Int)(_for_it_67_0 Int)(_for_it_67_1 Int)) (and (= _for_it_67_0 _for_it_67_1) (= _for_it_66_0 _for_it_66_1) (= _for_it_65 (+ _for_it_65 1)) (<= (+ kidia (- 1)) _for_it_67_0) (<= _for_it_67_0 (+ kfdia (- 1))) (<= _for_it_67_1 (+ kfdia (- 1))) (<= 0 _for_it_66_0) (<= _for_it_66_0 4) (<= 0 _for_it_66_1) (<= _for_it_66_1 4) (<= (+ kidia (- 1)) _for_it_67_1))) (exists ((_for_it_68_0 Int)(_for_it_68_1 Int)) (and (= _for_it_65 (+ _for_it_65 1)) (= _for_it_68_0 _for_it_68_1) (<= _for_it_68_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_68_1) (<= _for_it_68_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_68_0)))))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)