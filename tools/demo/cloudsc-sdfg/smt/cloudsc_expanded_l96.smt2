(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_46_val () (Array Int Int))
(declare-fun _if_cond_47_val () (Array Int Int))

(assert (forall ((_for_it_49 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_49)
      (<= (+ _for_it_49 1) 4)
      (not (or (exists ((_for_it_50_1 Int)(_for_it_50_0 Int)) (and (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50_0 (* _for_it_49 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50_1 (* (+ _for_it_49 1) (- kfdia kidia)) 1) kidia)) (<= _for_it_50_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_1) (<= _for_it_50_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_0) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 4) (* ncldtop 4))) 1) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 5) (* ncldtop 4))) 1))) (exists ((_for_it_50_1 Int)(_for_it_50_0 Int)) (and (<= _for_it_50_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_1) (<= _for_it_50_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_0) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 4) (* ncldtop 4))) 1) (= _for_it_50_0 _for_it_50_1) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 5) (* ncldtop 4))) 1))) (exists ((_for_it_50_1 Int)(_for_it_50_0 Int)) (and (<= _for_it_50_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_1) (<= _for_it_50_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_0) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 4) (* ncldtop 4))) 1) (= _for_it_50_0 _for_it_50_1) (= _for_it_49 (+ _for_it_49 1)) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 5) (* ncldtop 4))) 1))) (= (- (+ (* 4 _for_it_23) _for_it_49 4) (* ncldtop 4)) (- (+ (* 4 _for_it_23) _for_it_49 5) (* ncldtop 4))) (exists ((_for_it_50_1 Int)(_for_it_50_0 Int)) (and (<= _for_it_50_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_1) (<= _for_it_50_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_0) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 4) (* ncldtop 4))) 1) (= _for_it_50_0 _for_it_50_1) (= _for_it_49 (+ _for_it_49 1)) (= (select _if_cond_47_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50_1 (* (+ _for_it_49 1) (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_47_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50_0 (* _for_it_49 (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 5) (* ncldtop 4))) 1))) (exists ((_for_it_50_1 Int)(_for_it_50_0 Int)) (and (<= _for_it_50_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_1) (<= _for_it_50_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_50_0) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 4) (* ncldtop 4))) 1) (= _for_it_50_0 _for_it_50_1) (= (select _if_cond_47_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50_1 (* (+ _for_it_49 1) (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_47_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_50_0 (* _for_it_49 (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_46_val (- (+ (* 4 _for_it_23) _for_it_49 5) (* ncldtop 4))) 1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)