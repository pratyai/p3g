(declare-fun _for_it_23 () Int)
(declare-fun _for_it_78 () Int)
(declare-fun _if_cond_76_val () (Array Int Int))

(assert (forall ((_for_it_80 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_80)
      (<= (+ _for_it_80 1) 4)
      (not (or (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81_0 (* _for_it_80 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81_1 (* (+ _for_it_80 1) (- kfdia kidia)) 1) kidia)) (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0))) (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0) (= _for_it_81_0 (- (+ _for_it_81_1 1) 1)) (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81_0 (* _for_it_80 (- kfdia kidia)) 1) kidia)) 1))) (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0) (= (- (+ _for_it_81_0 1) 1) _for_it_81_1) (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81_1 (* (+ _for_it_80 1) (- kfdia kidia)) 1) kidia)) 1))) (exists ((_for_it_81_0 Int)(_for_it_81_1 Int)) (and (<= _for_it_81_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_1) (<= _for_it_81_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_81_0) (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81_1 (* (+ _for_it_80 1) (- kfdia kidia)) 1) kidia)) 1) (= _for_it_81_0 _for_it_81_1) (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81_0 (* _for_it_80 (- kfdia kidia)) 1) kidia)) 1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)