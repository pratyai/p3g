(declare-fun _for_it_23 () Int)
(declare-fun _for_it_62 () Int)
(declare-fun _for_it_63 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_74_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_74_val (- (+ (* _for_it_62 (- kfdia kidia)) _for_it_63 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_74_val (- (+ (* _for_it_62 (- kfdia kidia)) _for_it_63 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
      (not (= _for_it_63 (+ _for_it_63 1)))
    )
    (or
      (not (= (select _if_cond_74_val (- (+ (* _for_it_62 (- kfdia kidia)) _for_it_63 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_74_val (- (+ (* _for_it_62 (- kfdia kidia)) _for_it_63 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
      (not (= _for_it_63 (+ _for_it_63 1)))
      (not (= 4 _for_it_62))
      (not (= _for_it_62 4))
    )
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_63 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_63)
    )
    (not (= (- (+ (* _for_it_62 (- kfdia kidia)) _for_it_63 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia) (- (+ (* _for_it_62 (- kfdia kidia)) _for_it_63 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)))
  )
))

(check-sat)