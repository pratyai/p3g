(declare-fun _for_it_23 () Int)
(declare-fun _for_it_59 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_70_val (Array Int Int)) (jn_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_70_val (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_70_val (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= _for_it_59 (+ _for_it_59 1)))
    )
    (or
      (not (= (select _if_cond_70_val (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
      (not (= 0 (+ (select jn_val (- (+ _for_it_23 1) ncldtop)) (- 1))))
      (not (= (+ (select jn_val (- (+ _for_it_23 1) ncldtop)) (- 1)) 0))
      (not (= (select _if_cond_70_val (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= _for_it_59 (+ _for_it_59 1)))
    )
    (or
      (not (= (select _if_cond_70_val (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_70_val (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
    )
    (not (= (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia) (- (+ _for_it_59 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)))
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_59 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_59)
      (<= kidia (+ kfdia (- 1)))
    )
  )
))

(check-sat)