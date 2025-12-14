(declare-fun _for_it_23 () Int)
(declare-fun _for_it_40 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_25_val (Array Int Int)))
  (and
    (not (= (- (+ _for_it_40 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia) (- (+ _for_it_40 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)))
    (or
      (not (= (select _if_cond_25_val (- (+ _for_it_40 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= _for_it_40 (+ _for_it_40 1)))
      (not (= (select _if_cond_25_val (- (+ _for_it_40 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_25_val (- (+ _for_it_40 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_25_val (- (+ _for_it_40 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
    )
    (and
      (<= (+ _for_it_40 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_40)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
  )
))

(check-sat)