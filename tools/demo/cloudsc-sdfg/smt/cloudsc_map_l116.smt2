

(assert (forall ((_for_it_69 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_69)
      (<= (+ _for_it_69 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_71_0 Int)(_for_it_70_0 Int)(_for_it_70_1 Int)(_for_it_71_1 Int)) (and (<= _for_it_71_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_71_1) (<= 0 _for_it_70_0) (<= _for_it_70_0 4) (<= _for_it_71_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_71_0) (<= 0 _for_it_70_1) (<= _for_it_70_1 4) (= _for_it_71_0 _for_it_71_1) (= _for_it_69 (+ _for_it_69 1)))))
    )
    false
  )
))

(check-sat)