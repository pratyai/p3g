(declare-fun _for_it_23 () Int)
(declare-fun _for_it_78 () Int)
(declare-fun _for_it_80 () Int)
(declare-fun _for_it_81 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_76_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_76_val (- (+ (* _for_it_80 (- kfdia kidia)) _for_it_81 (* _for_it_78 (- (* kfdia 4) (* kidia 4))) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 2) kidia)) 1))
      (not (= _for_it_81 (+ _for_it_81 1)))
      (not (= (select _if_cond_76_val (- (+ (* _for_it_80 (- kfdia kidia)) _for_it_81 (* _for_it_78 (- (* kfdia 4) (* kidia 4))) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_76_val (- (+ (* _for_it_80 (- kfdia kidia)) _for_it_81 (* _for_it_78 (- (* kfdia 4) (* kidia 4))) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 1) kidia)) 1))
      (not (= _for_it_81 (- (+ _for_it_81 2) 1)))
    )
    (or
      (not (= (select _if_cond_76_val (- (+ (* _for_it_80 (- kfdia kidia)) _for_it_81 (* _for_it_78 (- (* kfdia 4) (* kidia 4))) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 2) kidia)) 1))
      (not (= (- (+ _for_it_81 1) 1) (+ _for_it_81 1)))
    )
    (not (= (- (+ (* _for_it_80 (- kfdia kidia)) _for_it_81 (* _for_it_78 (- (* kfdia 4) (* kidia 4))) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 1) kidia) (- (+ (* _for_it_80 (- kfdia kidia)) _for_it_81 (* _for_it_78 (- (* kfdia 4) (* kidia 4))) (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 16) (* kidia 16))) 2) kidia)))
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_81 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_81)
    )
  )
))

(check-sat)