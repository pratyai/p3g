(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_22_val () (Array Int Int))

(assert (forall ((_for_it_37 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_37 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_37)
      (not (or (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_37 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_37 2) kidia)) (and (= _for_it_37 (+ _for_it_37 1)) (= (select _if_cond_22_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_37 2) kidia)) 1) (= (select _if_cond_22_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_37 1) kidia)) 1)) (and (= _for_it_37 (+ _for_it_37 1)) (= (select _if_cond_22_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_37 1) kidia)) 1)) (and (= _for_it_37 (+ _for_it_37 1)) (= (select _if_cond_22_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_37 2) kidia)) 1)) (= _for_it_37 (+ _for_it_37 1))))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)