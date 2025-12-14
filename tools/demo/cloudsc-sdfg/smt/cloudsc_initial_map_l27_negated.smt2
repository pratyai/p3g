(declare-fun _for_it_13 () Int)
(declare-fun _for_it_14 () Int)
(declare-fun _for_it_15 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (forall ((_if_cond_2_val (Array Int Int)) (_if_cond_3_val (Array Int Int)) (_if_cond_4_val (Array Int Int)))
  (and
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= _for_it_15 (+ _for_it_15 1)))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (and
        (or
          (not (= _for_it_13 4))
          (not (= _for_it_15 (+ _for_it_15 1)))
        )
        (not (= _for_it_15 (+ _for_it_15 1)))
      )
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= _for_it_13 (- (+ _for_it_13 1) 1)))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= _for_it_15 (- (+ _for_it_15 2) 1)))
      (not (= _for_it_14 (- (+ _for_it_14 1) 1)))
    )
    (and
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_15 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_15)
      (<= kidia (+ kfdia (- 1)))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (and
        (not (= _for_it_15 (+ _for_it_15 1)))
        (or
          (not (= 4 _for_it_13))
          (not (= _for_it_15 (+ _for_it_15 1)))
        )
      )
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (and
        (or
          (not (= _for_it_13 4))
          (not (= _for_it_15 (+ _for_it_15 1)))
        )
        (not (= _for_it_15 (+ _for_it_15 1)))
        (or
          (not (= 4 _for_it_13))
          (not (= _for_it_15 (+ _for_it_15 1)))
        )
      )
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= 4 _for_it_13))
      (not (= _for_it_15 (+ _for_it_15 1)))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= _for_it_15 (- (+ _for_it_15 2) 1)))
      (not (= _for_it_14 (- (+ _for_it_14 1) 1)))
      (not (= 4 (- (+ _for_it_13 1) 1)))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_4_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_4_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= _for_it_15 (+ _for_it_15 1)))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_3_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_4_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= _for_it_15 (+ _for_it_15 1)))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_4_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (not (= (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia) (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)))
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia) (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)))
    )
    (or
      (not (= (select _if_cond_3_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_4_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= _for_it_15 (+ _for_it_15 1)))
    )
    (or
      (not (= (select _if_cond_3_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_3_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= _for_it_15 (+ _for_it_15 1)))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_3_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= _for_it_13 4))
      (not (= _for_it_15 (+ _for_it_15 1)))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_4_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_3_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 1) kidia)) 1))
    )
    (or
      (not (= (- (+ _for_it_15 1) 1) (+ _for_it_15 1)))
      (not (= (- (+ _for_it_14 1) 1) _for_it_14))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
      (not (= (- (+ _for_it_13 1) 1) _for_it_13))
    )
    (or
      (not (= (- (+ _for_it_15 1) 1) (+ _for_it_15 1)))
      (not (= (- (+ _for_it_14 1) 1) _for_it_14))
      (not (= (- (+ _for_it_13 1) 1) 4))
      (not (= (select _if_cond_2_val (- (+ (* _for_it_14 (- kfdia kidia)) _for_it_15 (* _for_it_13 (- kfdia kidia) (+ klev (- 1))) 2) kidia)) 1))
    )
  )
))

(check-sat)