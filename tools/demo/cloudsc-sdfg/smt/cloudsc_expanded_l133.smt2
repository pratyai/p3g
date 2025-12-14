(declare-fun _for_it_23 () Int)
(declare-fun _for_it_85 () Int)
(declare-fun jo_val () (Array Int Int))

(assert (forall ((_for_it_86 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (exists ((_for_it_87_1 Int)(_for_it_87_0 Int)) (and (= (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_86 (* _for_it_85 (- kfdia kidia)) 1) kidia)) (- 1)) (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_86 (* _for_it_85 (- kfdia kidia)) 2) kidia)) (- 1))) (<= 0 _for_it_87_0) (<= _for_it_87_0 4) (<= 0 _for_it_87_1) (<= _for_it_87_1 4) (= _for_it_86 (+ _for_it_86 1)) (= _for_it_87_0 _for_it_87_1))) (exists ((tmp_parfor_0_0 Int)) (and (<= 0 tmp_parfor_0_0) (<= tmp_parfor_0_0 4) (= _for_it_86 (+ _for_it_86 1)))) (and (= (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_86 (* _for_it_85 (- kfdia kidia)) 1) kidia)) (- 1)) (+ (select jo_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_86 (* _for_it_85 (- kfdia kidia)) 2) kidia)) (- 1))) (= _for_it_86 (+ _for_it_86 1))) (exists ((tmp_parfor_0_0 Int)(tmp_parfor_0_1 Int)) (and (<= tmp_parfor_0_1 4) (<= 0 tmp_parfor_0_0) (<= tmp_parfor_0_0 4) (= _for_it_86 (+ _for_it_86 1)) (<= 0 tmp_parfor_0_1))) (= _for_it_86 (+ _for_it_86 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_86 (* _for_it_85 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 4) (* kidia 4))) _for_it_86 (* _for_it_85 (- kfdia kidia)) 2) kidia)) (exists ((tmp_parfor_0_1 Int)) (and (<= tmp_parfor_0_1 4) (= _for_it_86 (+ _for_it_86 1)) (<= 0 tmp_parfor_0_1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_86 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_86)
    )
    false
  )
))

(check-sat)