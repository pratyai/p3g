(declare-fun _for_it_11 () Int)
(declare-fun _if_cond_1_val () (Array Int Int))

(assert (forall ((_for_it_12 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ kidia (- 1)) _for_it_12)
      (not (or (= (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 1) kidia) (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 2) kidia)) (and (= (- (+ _for_it_11 1) 1) _for_it_11) (= (- (+ _for_it_12 1) 1) (+ _for_it_12 1)) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 2) kidia)) 1)) (and (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 2) kidia)) 1) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 1) kidia)) 1)) (and (= _for_it_11 (- (+ _for_it_11 1) 1)) (= _for_it_12 (- (+ _for_it_12 2) 1)) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 1) kidia)) 1)) (and (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 2) kidia)) 1) (= _for_it_12 (+ _for_it_12 1)) (= (select _if_cond_1_val (- (+ (* _for_it_11 (- kfdia kidia)) _for_it_12 1) kidia)) 1))))
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_12 1) (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)