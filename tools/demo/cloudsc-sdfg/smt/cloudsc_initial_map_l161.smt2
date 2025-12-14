(declare-fun _for_it_107 () Int)
(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_79_val () (Array Int Int))

(assert (forall ((_for_it_108 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_108 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_108)
      (not (or (and (= (- (+ _for_it_107 1) 1) 4) (= (- (+ _for_it_108 1) 1) (+ _for_it_108 1)) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia)) 1)) (and (= (- (+ _for_it_107 1) 1) _for_it_107) (= (- (+ _for_it_108 1) 1) (+ _for_it_108 1)) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia)) 1)) (and (= _for_it_108 (- (+ _for_it_108 2) 1)) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia)) 1) (= 4 (- (+ _for_it_107 1) 1))) (and (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia)) 1) (or (= _for_it_108 (+ _for_it_108 1)) (and (= _for_it_108 (+ _for_it_108 1)) (= _for_it_107 4)) (and (= _for_it_108 (+ _for_it_108 1)) (= 4 _for_it_107))) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia)) 1)) (and (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia)) 1) (or (= _for_it_108 (+ _for_it_108 1)) (and (= _for_it_108 (+ _for_it_108 1)) (= 4 _for_it_107))) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia)) 1)) (and (= _for_it_107 (- (+ _for_it_107 1) 1)) (= _for_it_108 (- (+ _for_it_108 2) 1)) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia)) 1)) (and (or (= _for_it_108 (+ _for_it_108 1)) (and (= _for_it_108 (+ _for_it_108 1)) (= _for_it_107 4))) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia)) 1)) (and (= _for_it_108 (+ _for_it_108 1)) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia)) 1) (= (select _if_cond_79_val (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia)) 1)) (= (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 1) kidia) (- (+ (* (- (+ _for_it_23 1) ncldtop) (- (* kfdia 3) (* kidia 3))) _for_it_108 (* _for_it_107 (- kfdia kidia)) 2) kidia))))
    )
    false
  )
))

(check-sat)