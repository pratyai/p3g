(declare-fun _for_it_11 () Int)
(declare-fun _for_it_12 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (forall ((_if_cond_1_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_1_val (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_1_val (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 1) kidia)) 1))
      (not (= _for_it_12 (+ _for_it_12 1)))
    )
    (or
      (not (= _for_it_11 (- (+ _for_it_11 1) 1)))
      (not (= _for_it_12 (- (+ _for_it_12 2) 1)))
      (not (= (select _if_cond_1_val (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_1_val (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 2) kidia)) 1))
      (not (= (select _if_cond_1_val (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_1_val (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 2) kidia)) 1))
      (not (= (- (+ _for_it_12 1) 1) (+ _for_it_12 1)))
      (not (= (- (+ _for_it_11 1) 1) _for_it_11))
    )
    (not (= (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 1) kidia) (- (+ _for_it_12 (* _for_it_11 (- kfdia kidia)) 2) kidia)))
    (and
      (<= (+ kidia (- 1)) _for_it_12)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_12 1) (+ kfdia (- 1)))
    )
  )
))

(check-sat)