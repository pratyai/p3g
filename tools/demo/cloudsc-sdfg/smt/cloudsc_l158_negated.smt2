(declare-fun _for_it_105 () Int)
(declare-fun _for_it_106 () Int)
(declare-fun _for_it_23 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_55 () Int)

(assert (forall ((_for_it_105_norm_val (Array Int Int)))
  (and
    (and
      (<= (+ kidia (- 1)) tmp_parfor_55)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_55 1) (+ kfdia (- 1)))
    )
    (not (= tmp_parfor_55 (+ tmp_parfor_55 1)))
    (or
      (not (= _for_it_106 (select _for_it_105_norm_val (- (+ _for_it_105 (* 3 _for_it_23) 3) (* ncldtop 3)))))
      (not (= tmp_parfor_55 (+ tmp_parfor_55 1)))
    )
    (or
      (not (= tmp_parfor_55 (+ tmp_parfor_55 1)))
      (not (= (select _for_it_105_norm_val (- (+ _for_it_105 (* 3 _for_it_23) 3) (* ncldtop 3))) _for_it_106))
    )
  )
))

(check-sat)