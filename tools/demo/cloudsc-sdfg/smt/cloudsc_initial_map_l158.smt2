(declare-fun _for_it_105 () Int)
(declare-fun _for_it_105_norm_val () (Array Int Int))
(declare-fun _for_it_106 () Int)
(declare-fun _for_it_23 () Int)

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_55 Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_55 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) tmp_parfor_55)
      (not (or (and (= tmp_parfor_55 (+ tmp_parfor_55 1)) (= (select _for_it_105_norm_val (- (+ (* 3 _for_it_23) _for_it_105 3) (* ncldtop 3))) _for_it_106)) (= tmp_parfor_55 (+ tmp_parfor_55 1)) (and (= _for_it_106 (select _for_it_105_norm_val (- (+ (* 3 _for_it_23) _for_it_105 3) (* ncldtop 3)))) (= tmp_parfor_55 (+ tmp_parfor_55 1)))))
    )
    false
  )
))

(check-sat)