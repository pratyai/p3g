(declare-fun _if_cond_5_val () (Array Int Int))

(assert (forall ((_for_it_18 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_18)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_18 1) (+ klev (- 1)))
      (not (or (exists ((_for_it_19_0 Int)(_for_it_19_1 Int)) (and (not (= (select _if_cond_5_val 0) 1)) (<= _for_it_19_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_1) (<= _for_it_19_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_0) (= _for_it_19_0 _for_it_19_1) (= _for_it_18 (+ _for_it_18 1)))) (exists ((_for_it_19_0 Int)(_for_it_19_1 Int)) (and (= (select _if_cond_5_val 0) 1) (<= _for_it_19_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_1) (<= _for_it_19_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_0) (= _for_it_19_0 _for_it_19_1) (= _for_it_18 (+ _for_it_18 1)))) (exists ((_for_it_19_0 Int)(_for_it_19_1 Int)) (and (<= _for_it_19_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_1) (<= _for_it_19_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_0) (= _for_it_19_0 _for_it_19_1))) (exists ((_for_it_19_0 Int)(_for_it_19_1 Int)) (and (<= (+ kidia (- 1)) _for_it_19_0) (<= _for_it_19_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_1) (<= _for_it_19_0 (+ kfdia (- 1))))) (exists ((_for_it_19_0 Int)(_for_it_19_1 Int)) (and (<= _for_it_19_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_1) (<= _for_it_19_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_19_0) (= _for_it_19_0 _for_it_19_1) (= _for_it_18 (+ _for_it_18 1))))))
    )
    false
  )
))

(check-sat)