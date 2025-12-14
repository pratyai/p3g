(declare-fun _for_it_23 () Int)
(declare-fun _for_it_78 () Int)
(declare-fun _for_it_80 () Int)
(declare-fun _if_cond_76_val () (Array Int Int))

(assert (forall ((_for_it_81 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_81 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_81)
      (not (or (and (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81 (* _for_it_80 (- kfdia kidia)) 1) kidia)) 1) (= _for_it_81 (- (+ _for_it_81 2) 1))) (and (= _for_it_81 (+ _for_it_81 1)) (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81 (* _for_it_80 (- kfdia kidia)) 2) kidia)) 1) (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81 (* _for_it_80 (- kfdia kidia)) 1) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81 (* _for_it_80 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81 (* _for_it_80 (- kfdia kidia)) 2) kidia)) (and (= (select _if_cond_76_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* _for_it_78 (- (* kfdia 4) (* kidia 4))) _for_it_81 (* _for_it_80 (- kfdia kidia)) 2) kidia)) 1) (= (- (+ _for_it_81 1) 1) (+ _for_it_81 1)))))
    )
    false
  )
))

(check-sat)