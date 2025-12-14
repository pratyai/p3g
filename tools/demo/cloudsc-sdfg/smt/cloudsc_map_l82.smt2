(declare-fun _for_it_23 () Int)
(declare-fun _if_cond_21_val () (Array Int Int))

(assert (forall ((_for_it_35 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 0 _for_it_35)
      (<= (+ _for_it_35 1) 4)
      (<= ncldtop (+ klev (- 1)))
      (not (or (exists ((_for_it_36_0 Int)(_for_it_36_1 Int)) (and (<= _for_it_36_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_0) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 5) (* ncldtop 4))) 1) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 4) (* ncldtop 4))) 1) (<= _for_it_36_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_1) (= _for_it_36_0 _for_it_36_1))) (exists ((_for_it_36_0 Int)(_for_it_36_1 Int)) (and (<= _for_it_36_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_0) (= _for_it_35 (+ _for_it_35 1)) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 5) (* ncldtop 4))) 1) (= 4 (+ _for_it_35 1)) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 4) (* ncldtop 4))) 1) (<= _for_it_36_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_1) (= _for_it_36_0 _for_it_36_1))) (exists ((_for_it_36_0 Int)(_for_it_36_1 Int)) (and (<= _for_it_36_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_0) (= _for_it_35 4) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 5) (* ncldtop 4))) 1) (= 4 (+ _for_it_35 1)) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 4) (* ncldtop 4))) 1) (<= _for_it_36_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_1) (= _for_it_36_0 _for_it_36_1))) (exists ((_for_it_36_0 Int)(_for_it_36_1 Int)) (and (<= _for_it_36_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_0) (= _for_it_35 (+ _for_it_35 1)) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 5) (* ncldtop 4))) 1) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 4) (* ncldtop 4))) 1) (<= _for_it_36_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_1) (= _for_it_36_0 _for_it_36_1))) (= (- (+ (* 4 _for_it_23) _for_it_35 4) (* ncldtop 4)) (- (+ (* 4 _for_it_23) _for_it_35 5) (* ncldtop 4))) (exists ((_for_it_36_0 Int)(_for_it_36_1 Int)) (and (<= _for_it_36_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_0) (= _for_it_35 (+ _for_it_35 1)) (= _for_it_35 4) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 5) (* ncldtop 4))) 1) (= (select _if_cond_21_val (- (+ (* 4 _for_it_23) _for_it_35 4) (* ncldtop 4))) 1) (<= _for_it_36_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_36_1) (= _for_it_36_0 _for_it_36_1)))))
    )
    false
  )
))

(check-sat)