(declare-fun _for_it_114 () Int)
(declare-fun _for_it_23 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_80_val (Array Int Int)))
  (and
    (or
      (not (= _for_it_114 (+ _for_it_114 1)))
      (not (= (select _if_cond_80_val (- (+ _for_it_114 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia)) 1))
      (not (= (select _if_cond_80_val (- (+ _for_it_114 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)) 1))
    )
    (not (= (- (+ _for_it_114 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 1) kidia) (- (+ _for_it_114 (* (- (+ _for_it_23 1) ncldtop) (- kfdia kidia)) 2) kidia)))
    (and
      (<= (+ _for_it_114 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_114)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
  )
))

(check-sat)