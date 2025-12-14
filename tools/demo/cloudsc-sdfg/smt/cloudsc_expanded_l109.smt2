(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_73_val () (Array Int Int))
(declare-fun _if_cond_74_val () (Array Int Int))

(assert (forall ((_for_it_62 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= 0 _for_it_62)
      (<= (+ _for_it_62 1) 4)
      (not (or (exists ((_for_it_63_1 Int)(_for_it_63_0 Int)) (and (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_63_0 (* _for_it_62 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_63_1 (* (+ _for_it_62 1) (- kfdia kidia)) 1) kidia)) (<= _for_it_63_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_63_1) (= (select _if_cond_73_val (- (+ (* 4 _for_it_23) _for_it_62 5) (* ncldtop 4))) 1) (<= _for_it_63_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_63_0) (= (select _if_cond_73_val (- (+ (* 4 _for_it_23) _for_it_62 4) (* ncldtop 4))) 1))) (exists ((_for_it_63_1 Int)(_for_it_63_0 Int)) (and (= 4 (+ _for_it_62 1)) (= (select _if_cond_74_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_63_1 (* (+ _for_it_62 1) (- kfdia kidia)) 1) kidia)) 1) (<= _for_it_63_1 (+ kfdia (- 1))) (= (select _if_cond_74_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_63_0 (* _for_it_62 (- kfdia kidia)) 1) kidia)) 1) (= _for_it_63_0 _for_it_63_1) (<= (+ kidia (- 1)) _for_it_63_1) (= (select _if_cond_73_val (- (+ (* 4 _for_it_23) _for_it_62 5) (* ncldtop 4))) 1) (<= _for_it_63_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_63_0) (= _for_it_62 4) (= (select _if_cond_73_val (- (+ (* 4 _for_it_23) _for_it_62 4) (* ncldtop 4))) 1))) (exists ((_for_it_63_1 Int)(_for_it_63_0 Int)) (and (= (select _if_cond_74_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_63_1 (* (+ _for_it_62 1) (- kfdia kidia)) 1) kidia)) 1) (<= _for_it_63_1 (+ kfdia (- 1))) (= (select _if_cond_74_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_63_0 (* _for_it_62 (- kfdia kidia)) 1) kidia)) 1) (= _for_it_63_0 _for_it_63_1) (<= (+ kidia (- 1)) _for_it_63_1) (= _for_it_62 (+ _for_it_62 1)) (= (select _if_cond_73_val (- (+ (* 4 _for_it_23) _for_it_62 5) (* ncldtop 4))) 1) (<= _for_it_63_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_63_0) (= (select _if_cond_73_val (- (+ (* 4 _for_it_23) _for_it_62 4) (* ncldtop 4))) 1))) (= (- (+ (* 4 _for_it_23) _for_it_62 4) (* ncldtop 4)) (- (+ (* 4 _for_it_23) _for_it_62 5) (* ncldtop 4)))))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)