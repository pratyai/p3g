

(assert (forall ((_for_it_105 Int) (_for_it_105_norm_val (Array Int Int)) (_for_it_106 Int) (_for_it_23 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= (+ _for_it_106 1) 4)
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((tmp_parfor_55_1 Int)(tmp_parfor_55_0 Int)) (and (<= (+ kidia (- 1)) tmp_parfor_55_0) (or (and (= (select _for_it_105_norm_val (- (+ (* 3 _for_it_23) _for_it_105 3) (* ncldtop 3))) (+ _for_it_106 1)) (= tmp_parfor_55_0 tmp_parfor_55_1)) (= tmp_parfor_55_0 tmp_parfor_55_1) (and (= tmp_parfor_55_0 tmp_parfor_55_1) (= _for_it_106 (select _for_it_105_norm_val (- (+ (* 3 _for_it_23) _for_it_105 3) (* ncldtop 3)))))) (<= tmp_parfor_55_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_55_1) (<= tmp_parfor_55_0 (+ kfdia (- 1))))))
      (<= (+ (select _for_it_105_norm_val (- (+ _for_it_105 (* 3 _for_it_23) 3) (* ncldtop 3))) 1) _for_it_106)
      (<= (+ (select _for_it_105_norm_val (- (+ _for_it_105 (* 3 _for_it_23) 3) (* ncldtop 3))) 2) 4)
    )
    false
  )
))

(check-sat)