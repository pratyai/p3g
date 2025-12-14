(declare-fun _if_cond_1_val () (Array Int Int))

(assert (forall ((_for_it_11 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_11)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (not (or (exists ((_for_it_12_1 Int)(_for_it_12_0 Int)) (and (<= _for_it_12_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_1) (<= _for_it_12_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_0) (= (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12_0 1) kidia) (- (+ (* (+ _for_it_11 1) (- kfdia kidia)) _for_it_12_1 1) kidia)))) (exists ((_for_it_12_1 Int)(_for_it_12_0 Int)) (and (<= _for_it_12_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_1) (<= _for_it_12_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_0) (= (- (+ _for_it_11 1) 1) (+ _for_it_11 1)) (= (- (+ _for_it_12_0 1) 1) _for_it_12_1) (= (select _if_cond_1_val (- (+ (* (+ _for_it_11 1) (- kfdia kidia)) _for_it_12_1 1) kidia)) 1))) (exists ((_for_it_12_1 Int)(_for_it_12_0 Int)) (and (<= _for_it_12_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_1) (<= _for_it_12_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_0) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12_0 1) kidia)) 1) (= (select _if_cond_1_val (- (+ (* (+ _for_it_11 1) (- kfdia kidia)) _for_it_12_1 1) kidia)) 1))) (exists ((_for_it_12_1 Int)(_for_it_12_0 Int)) (and (<= _for_it_12_1 (+ kfdia (- 1))) (= _for_it_11 (- (+ _for_it_11 2) 1)) (<= (+ kidia (- 1)) _for_it_12_1) (<= _for_it_12_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_0) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12_0 1) kidia)) 1) (= _for_it_12_0 (- (+ _for_it_12_1 1) 1)))) (exists ((_for_it_12_1 Int)(_for_it_12_0 Int)) (and (<= _for_it_12_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_1) (= _for_it_12_0 _for_it_12_1) (= _for_it_11 (+ _for_it_11 1)) (<= _for_it_12_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_12_0) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12_0 1) kidia)) 1) (= (select _if_cond_1_val (- (+ (* (+ _for_it_11 1) (- kfdia kidia)) _for_it_12_1 1) kidia)) 1)))))
      (<= (+ _for_it_11 1) (+ klev (- 1)))
    )
    false
  )
))

(check-sat)