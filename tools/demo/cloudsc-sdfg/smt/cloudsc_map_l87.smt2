(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_25_val () (Array Int Int))

(assert (forall ((_for_it_40 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_40 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_40)
      (not (or (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_40 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_40 2) kidia)) (and (= (select _if_cond_25_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_40 2) kidia)) 1) (= (select _if_cond_25_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_40 1) kidia)) 1)) (and (= (select _if_cond_25_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_40 2) kidia)) 1) (= (select _if_cond_25_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_40 1) kidia)) 1) (= _for_it_40 (+ _for_it_40 1)))))
    )
    false
  )
))

(check-sat)