(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_27_val () (Array Int Int))

(assert (forall ((_for_it_44 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (and (= (select _if_cond_27_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_44 2) kidia)) 1) (= (select _if_cond_27_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_44 1) kidia)) 1)) (and (= _for_it_44 (+ _for_it_44 1)) (= (select _if_cond_27_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_44 2) kidia)) 1) (= (select _if_cond_27_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_44 1) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_44 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_44 2) kidia))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_44 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_44)
    )
    false
  )
))

(check-sat)