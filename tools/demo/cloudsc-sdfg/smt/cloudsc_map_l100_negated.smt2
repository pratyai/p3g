(declare-fun _for_it_23 () Int)
(declare-fun _for_it_53 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_59_val (Array Int Int)) (_if_cond_60_val (Array Int Int)))
  (and
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_53 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_53)
      (<= kidia (+ kfdia (- 1)))
    )
    (or
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_60_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_60_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= _for_it_53 (+ _for_it_53 1)))
    )
    (or
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_60_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_60_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_60_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_60_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
    )
    (not (= (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia) (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)))
    (or
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_59_val (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia) (- (+ _for_it_53 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)))
    )
  )
))

(check-sat)