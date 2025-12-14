(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_59_val () (Array Int Int))
(declare-fun _if_cond_60_val () (Array Int Int))

(assert (forall ((_for_it_53 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) (and (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia))) (and (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1)) (and (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= (select _if_cond_60_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1)) (and (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (select _if_cond_60_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1)) (and (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= (select _if_cond_60_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (select _if_cond_60_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1)) (and (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= (select _if_cond_59_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (select _if_cond_60_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 2) kidia)) 1) (= (select _if_cond_60_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_53 1) kidia)) 1) (= _for_it_53 (+ _for_it_53 1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_53 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_53)
    )
    false
  )
))

(check-sat)