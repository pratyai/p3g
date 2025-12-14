(declare-fun _for_it_23 () Int)
(declare-fun _for_it_78 () Int)
(declare-fun _for_it_82 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((jo_val (Array Int Int)))
  (and
    (or
      (not (= _for_it_82 (+ _for_it_82 1)))
      (not (= (+ (select jo_val (- (+ (* _for_it_78 (- kfdia kidia)) _for_it_82 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) (- 1)) (+ (select jo_val (- (+ (* _for_it_78 (- kfdia kidia)) _for_it_82 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) (- 1))))
    )
    (not (= (- (+ (* _for_it_78 (- kfdia kidia)) _for_it_82 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia) (- (+ (* _for_it_78 (- kfdia kidia)) _for_it_82 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)))
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_82 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_82)
    )
  )
))

(check-sat)