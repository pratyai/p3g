(declare-fun _for_it_23 () Int)
(declare-fun _for_it_55 () Int)
(declare-fun _if_cond_63_val () (Array Int Int))
(declare-fun jn_val () (Array Int Int))

(assert (forall ((_for_it_56 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= (+ _for_it_56 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_56)
      (not (or (and (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 2) kidia)) 1) (= _for_it_56 (+ _for_it_56 1)) (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 1) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 2) kidia)) (and (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 2) kidia)) 1) (= _for_it_56 (+ _for_it_56 1)) (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 1) kidia)) 1) (= _for_it_55 (+ (select jn_val (- (+ (* 4 _for_it_23) _for_it_55 4) (* ncldtop 4))) (- 1)))) (and (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 2) kidia)) 1) (= _for_it_56 (+ _for_it_56 1)) (= (+ (select jn_val (- (+ (* 4 _for_it_23) _for_it_55 4) (* ncldtop 4))) (- 1)) _for_it_55) (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 1) kidia)) 1)) (and (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 2) kidia)) 1) (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 1) kidia)) 1)) (and (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_63_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_56 (* _for_it_55 (- kfdia kidia)) 2) kidia)) 1) (= _for_it_56 (+ _for_it_56 1)) (= _for_it_55 (+ (select jn_val (- (+ (* 4 _for_it_23) _for_it_55 4) (* ncldtop 4))) (- 1))) (= (+ (select jn_val (- (+ (* 4 _for_it_23) _for_it_55 4) (* ncldtop 4))) (- 1)) _for_it_55))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)