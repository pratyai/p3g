(declare-fun _for_it_23 () Int)
(declare-fun _for_it_85 () Int)
(declare-fun _for_it_89 () Int)
(declare-fun _if_cond_77_val () (Array Int Int))
(declare-fun jo_val () (Array Int Int))

(assert (forall ((_for_it_90 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_90)
      (<= (+ _for_it_90 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (not (or (and (= (select _if_cond_77_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* 4 _for_it_89) _for_it_90 (* _for_it_85 (- (* kfdia 4) (* kidia 4))) 5) (* kidia 4))) 1) (= _for_it_90 (+ _for_it_90 1)) (= (select _if_cond_77_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* 4 _for_it_89) _for_it_90 (* _for_it_85 (- (* kfdia 4) (* kidia 4))) 4) (* kidia 4))) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* 4 _for_it_89) _for_it_90 (* _for_it_85 (- (* kfdia 4) (* kidia 4))) 4) (* kidia 4)) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* 4 _for_it_89) _for_it_90 (* _for_it_85 (- (* kfdia 4) (* kidia 4))) 5) (* kidia 4))) (and (= (select _if_cond_77_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* 4 _for_it_89) _for_it_90 (* _for_it_85 (- (* kfdia 4) (* kidia 4))) 5) (* kidia 4))) 1) (= (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_89 (* _for_it_85 (- kfdia kidia)) 1) kidia)) (- 1)) (+ _for_it_90 1)) (= _for_it_90 (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_89 (* _for_it_85 (- kfdia kidia)) 1) kidia)) (- 1))) (= (select _if_cond_77_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) (* 4 _for_it_89) _for_it_90 (* _for_it_85 (- (* kfdia 4) (* kidia 4))) 4) (* kidia 4))) 1))))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)