(declare-fun _for_it_23 () Int)
(declare-fun _for_it_85 () Int)
(declare-fun _for_it_88 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((jo_val (Array Int Int)))
  (and
    (and
      (<= (+ _for_it_88 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_88)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    (or
      (not (= (+ (select jo_val (- (+ (* _for_it_85 (- kfdia kidia)) _for_it_88 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia)) (- 1)) (+ (select jo_val (- (+ (* _for_it_85 (- kfdia kidia)) _for_it_88 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)) (- 1))))
      (not (= _for_it_88 (+ _for_it_88 1)))
    )
    (not (= (- (+ (* _for_it_85 (- kfdia kidia)) _for_it_88 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 1) kidia) (- (+ (* _for_it_85 (- kfdia kidia)) _for_it_88 (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) 2) kidia)))
    (not (= _for_it_88 (+ _for_it_88 1)))
  )
))

(check-sat)