(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_70_val () (Array Int Int))
(declare-fun jn_val () (Array Int Int))

(assert (forall ((_for_it_59 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (and (= (select _if_cond_70_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 2) kidia)) 1) (= (select _if_cond_70_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 1) kidia)) 1)) (and (= 0 (+ (select jn_val (- (+ _for_it_23 1) ncldtop)) (- 1))) (= (+ (select jn_val (- (+ _for_it_23 1) ncldtop)) (- 1)) 0) (= _for_it_59 (+ _for_it_59 1)) (= (select _if_cond_70_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 2) kidia)) 1) (= (select _if_cond_70_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 1) kidia)) 1)) (and (= _for_it_59 (+ _for_it_59 1)) (= (select _if_cond_70_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 2) kidia)) 1) (= (select _if_cond_70_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 1) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_59 2) kidia))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_59 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_59)
    )
    false
  )
))

(check-sat)