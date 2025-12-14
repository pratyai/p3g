(declare-fun _for_it_23 () Int)
(declare-fun _for_it_55 () Int)
(declare-fun _for_it_56 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_63_val (Array Int Int)) (jn_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
      (not (= _for_it_56 (+ _for_it_56 1)))
      (not (= _for_it_55 (+ (select jn_val (- (+ _for_it_55 (* 4 _for_it_23) 4) (* ncldtop 4))) (- 1))))
      (not (= (+ (select jn_val (- (+ _for_it_55 (* 4 _for_it_23) 4) (* ncldtop 4))) (- 1)) _for_it_55))
    )
    (or
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
    )
    (or
      (not (= _for_it_56 (+ _for_it_56 1)))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
      (not (= (+ (select jn_val (- (+ _for_it_55 (* 4 _for_it_23) 4) (* ncldtop 4))) (- 1)) _for_it_55))
    )
    (or
      (not (= _for_it_56 (+ _for_it_56 1)))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
      (not (= _for_it_55 (+ (select jn_val (- (+ _for_it_55 (* 4 _for_it_23) 4) (* ncldtop 4))) (- 1))))
    )
    (not (= (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia) (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)))
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_56 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_56)
    )
    (or
      (not (= _for_it_56 (+ _for_it_56 1)))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_63_val (- (+ (* _for_it_55 (- kfdia kidia)) _for_it_56 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
    )
  )
))

(check-sat)