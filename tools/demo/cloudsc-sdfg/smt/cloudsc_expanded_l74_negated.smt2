(declare-fun _for_it_23 () Int)
(declare-fun _for_it_27 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_8_val (Array Int Int)) (_if_cond_9_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_8_val (- (+ _for_it_27 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_8_val (- (+ _for_it_27 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= _for_it_27 (+ _for_it_27 1)))
    )
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_27 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_27)
    )
    (or
      (not (= (select _if_cond_9_val (- (+ _for_it_27 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= _for_it_27 (+ _for_it_27 1)))
      (not (= (select _if_cond_9_val (- (+ _for_it_27 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
    )
    (not (= (- (+ _for_it_27 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia) (- (+ _for_it_27 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)))
  )
))

(check-sat)