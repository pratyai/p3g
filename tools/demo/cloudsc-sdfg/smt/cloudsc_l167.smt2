(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_80_val () (Array Int Int))

(assert (forall ((_for_it_114 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_114 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_114)
      (not (or (and (= (select _if_cond_80_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_114 1) kidia)) 1) (= _for_it_114 (+ _for_it_114 1)) (= (select _if_cond_80_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_114 2) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_114 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) _for_it_114 2) kidia))))
    )
    false
  )
))

(check-sat)