(declare-fun _for_it_23 () Int)
(declare-fun _for_it_49 () Int)
(declare-fun _for_it_50 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_47_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_47_val (- (+ (* _for_it_49 (- kfdia kidia)) _for_it_50 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) 1))
      (not (= (select _if_cond_47_val (- (+ (* _for_it_49 (- kfdia kidia)) _for_it_50 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) 1))
      (not (= _for_it_50 (+ _for_it_50 1)))
    )
    (not (= (- (+ (* _for_it_49 (- kfdia kidia)) _for_it_50 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia) (- (+ (* _for_it_49 (- kfdia kidia)) _for_it_50 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)))
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_50 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_50)
    )
    (not (= _for_it_50 (+ _for_it_50 1)))
  )
))

(check-sat)