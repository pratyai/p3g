(declare-fun _for_it_100 () Int)

(assert (forall ((_for_it_101 Int) (_for_it_99 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (exists ((_for_it_102_1 Int)(_for_it_102_0 Int)) (and (<= (+ kidia (- 1)) _for_it_102_1) (<= _for_it_102_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_102_0) (or (and (= _for_it_102_0 _for_it_102_1) (= _for_it_99 _for_it_100) (= _for_it_101 (+ _for_it_101 1))) (and (= _for_it_99 (+ _for_it_101 1)) (= _for_it_102_0 _for_it_102_1)) (and (= _for_it_102_0 _for_it_102_1) (= _for_it_101 (+ _for_it_101 1))) (and (= _for_it_101 _for_it_99) (= _for_it_102_0 _for_it_102_1)) (and (= _for_it_102_0 _for_it_102_1) (= _for_it_100 _for_it_99) (= _for_it_101 (+ _for_it_101 1)))) (<= _for_it_102_1 (+ kfdia (- 1))))))
      (<= (+ _for_it_101 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= (+ _for_it_99 2) 4)
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_99 1) _for_it_101)
    )
    false
  )
))

(check-sat)