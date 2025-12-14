(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_20_val () (Array Int Int))

(assert (forall ((_for_it_32 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (= (- (+ (* 4 _for_it_23) _for_it_32 4) (* ncldtop 4)) (- (+ (* 4 _for_it_23) _for_it_32 5) (* ncldtop 4))) (exists ((_for_it_33_0 Int)(_for_it_33_1 Int)) (and (<= _for_it_33_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_33_1) (<= _for_it_33_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_33_0) (= (select _if_cond_20_val (- (+ (* 4 _for_it_23) _for_it_32 5) (* ncldtop 4))) 1) (= (select _if_cond_20_val (- (+ (* 4 _for_it_23) _for_it_32 4) (* ncldtop 4))) 1) (= _for_it_33_0 _for_it_33_1) (= _for_it_32 (+ _for_it_32 1))))))
      (<= 0 _for_it_32)
      (<= (+ _for_it_32 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)