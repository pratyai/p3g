(declare-fun _for_it_23 () Int)
(declare-fun _for_it_49 () Int)
(declare-fun _if_cond_47_val () (Array Int Int))

(assert (forall ((_for_it_50 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_50 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_50)
      (not (or (and (= (select _if_cond_47_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50 (* _for_it_49 (- kfdia kidia)) 2) kidia)) 1) (= _for_it_50 (+ _for_it_50 1)) (= (select _if_cond_47_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50 (* _for_it_49 (- kfdia kidia)) 1) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50 (* _for_it_49 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50 (* _for_it_49 (- kfdia kidia)) 2) kidia)) (= _for_it_50 (+ _for_it_50 1))))
    )
    false
  )
))

(check-sat)