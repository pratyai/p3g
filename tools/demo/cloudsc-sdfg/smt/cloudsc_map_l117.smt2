

(assert (forall ((_for_it_70 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_70)
      (<= (+ _for_it_70 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((_for_it_71_1 Int)(_for_it_71_0 Int)) (and (= _for_it_71_0 _for_it_71_1) (<= _for_it_71_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_71_1) (<= _for_it_71_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_71_0))))
    )
    false
  )
))

(check-sat)