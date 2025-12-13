(declare-fun _if_cond_76_val () (Array Int Int))

(assert (forall ((_for_it_80 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (= _for_it_81_0 _for_it_81_1) (= (select _if_cond_76_val 0) 1) (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0))) (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (= (- (+ _for_it_81_0 1) 1) _for_it_81_1) (= (select _if_cond_76_val 0) 1) (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0))) (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0) (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1))) (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (= _for_it_81_0 (- (+ _for_it_81_1 1) 1)) (= (select _if_cond_76_val 0) 1) (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0)))))
      (<= 0 _for_it_80)
      (<= (+ _for_it_80 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)