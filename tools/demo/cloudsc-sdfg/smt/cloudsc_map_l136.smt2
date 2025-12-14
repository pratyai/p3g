(declare-fun _for_it_23 () Int)
(declare-fun _for_it_85 () Int)
(declare-fun jo_val () (Array Int Int))

(assert (forall ((_for_it_88 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_88 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_88)
      (not (or (= _for_it_88 (+ _for_it_88 1)) (and (= (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_88 (* _for_it_85 (- kfdia kidia)) 1) kidia)) (- 1)) (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_88 (* _for_it_85 (- kfdia kidia)) 2) kidia)) (- 1))) (= _for_it_88 (+ _for_it_88 1))) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_88 (* _for_it_85 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_88 (* _for_it_85 (- kfdia kidia)) 2) kidia))))
    )
    false
  )
))

(check-sat)