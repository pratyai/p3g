(declare-fun _for_it_107 () Int)
(declare-fun _for_it_108 () Int)
(declare-fun _for_it_23 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_if_cond_79_val (Array Int Int)))
  (and
    (or
      (not (= _for_it_107 (- (+ _for_it_107 1) 1)))
      (not (= _for_it_108 (- (+ _for_it_108 2) 1)))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)) 1))
      (and
        (or
          (not (= _for_it_108 (+ _for_it_108 1)))
          (not (= 4 _for_it_107))
        )
        (not (= _for_it_108 (+ _for_it_108 1)))
      )
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)) 1))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia)) 1))
      (and
        (or
          (not (= _for_it_108 (+ _for_it_108 1)))
          (not (= 4 _for_it_107))
        )
        (not (= _for_it_108 (+ _for_it_108 1)))
        (or
          (not (= _for_it_108 (+ _for_it_108 1)))
          (not (= _for_it_107 4))
        )
      )
    )
    (or
      (not (= 4 (- (+ _for_it_107 1) 1)))
      (not (= _for_it_108 (- (+ _for_it_108 2) 1)))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia)) 1))
    )
    (or
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)) 1))
      (not (= (- (+ _for_it_107 1) 1) _for_it_107))
      (not (= (- (+ _for_it_108 1) 1) (+ _for_it_108 1)))
    )
    (or
      (not (= (- (+ _for_it_107 1) 1) 4))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)) 1))
      (not (= (- (+ _for_it_108 1) 1) (+ _for_it_108 1)))
    )
    (not (= (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia) (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)))
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_108 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_108)
      (<= kidia (+ kfdia (- 1)))
    )
    (or
      (not (= _for_it_108 (+ _for_it_108 1)))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)) 1))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia)) 1))
    )
    (or
      (and
        (not (= _for_it_108 (+ _for_it_108 1)))
        (or
          (not (= _for_it_108 (+ _for_it_108 1)))
          (not (= _for_it_107 4))
        )
      )
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 2) kidia)) 1))
      (not (= (select _if_cond_79_val (- (+ (* _for_it_107 (- kfdia kidia)) _for_it_108 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) 1) kidia)) 1))
    )
  )
))

(check-sat)