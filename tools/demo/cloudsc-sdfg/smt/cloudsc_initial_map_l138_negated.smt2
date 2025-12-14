(declare-fun _for_it_23 () Int)
(declare-fun _for_it_85 () Int)
(declare-fun _for_it_89 () Int)
(declare-fun _for_it_90 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_77_val (Array Int Int)) (jo_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_77_val (- (+ (* _for_it_85 (- (* kfdia 4) (* kidia 4))) _for_it_90 (* 4 _for_it_89) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 4) (* kidia 4))) 1))
      (not (= (select _if_cond_77_val (- (+ (* _for_it_85 (- (* kfdia 4) (* kidia 4))) _for_it_90 (* 4 _for_it_89) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 5) (* kidia 4))) 1))
      (not (= _for_it_90 (+ (select jo_val (- (+ (* _for_it_85 (- kfdia kidia)) _for_it_89 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) (- 1))))
      (not (= (+ (select jo_val (- (+ (* _for_it_85 (- kfdia kidia)) _for_it_89 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) (- 1)) (+ _for_it_90 1)))
    )
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 0 _for_it_90)
      (<= (+ _for_it_90 1) 4)
      (<= ncldtop (+ klev (- 1)))
    )
    (not (= (- (+ (* _for_it_85 (- (* kfdia 4) (* kidia 4))) _for_it_90 (* 4 _for_it_89) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 4) (* kidia 4)) (- (+ (* _for_it_85 (- (* kfdia 4) (* kidia 4))) _for_it_90 (* 4 _for_it_89) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 5) (* kidia 4))))
    (or
      (not (= _for_it_90 (+ _for_it_90 1)))
      (not (= (select _if_cond_77_val (- (+ (* _for_it_85 (- (* kfdia 4) (* kidia 4))) _for_it_90 (* 4 _for_it_89) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 5) (* kidia 4))) 1))
      (not (= (select _if_cond_77_val (- (+ (* _for_it_85 (- (* kfdia 4) (* kidia 4))) _for_it_90 (* 4 _for_it_89) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 4) (* kidia 4))) 1))
    )
  )
))

(check-sat)