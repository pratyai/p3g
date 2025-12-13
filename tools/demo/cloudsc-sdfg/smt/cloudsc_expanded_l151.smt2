(declare-fun _for_it_100 () Int)
(declare-fun _for_it_101 () Int)
(declare-fun _for_it_99 () Int)

(assert (forall ((_for_it_102 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_102 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_102)
      (not (or (and (= _for_it_102 (+ _for_it_102 1)) (= _for_it_99 _for_it_100)) (and (= _for_it_99 _for_it_101) (= _for_it_102 (+ _for_it_102 1))) (and (= _for_it_102 (+ _for_it_102 1)) (= _for_it_100 _for_it_99)) (= _for_it_102 (+ _for_it_102 1)) (and (= _for_it_101 _for_it_99) (= _for_it_102 (+ _for_it_102 1)))))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)