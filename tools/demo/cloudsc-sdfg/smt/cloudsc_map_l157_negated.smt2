(declare-fun _for_it_105 () Int)
(declare-fun _for_it_106 () Int)
(declare-fun _for_it_23 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (forall ((_for_it_105_norm_val (Array Int Int)))
  (and
    (forall ((tmp_parfor_55_0 Int) (tmp_parfor_55_1 Int))
      (or
        (not (<= (+ kidia (- 1)) tmp_parfor_55_0))
        (and
          (or
            (not (= _for_it_106 (select _for_it_105_norm_val (- (+ _for_it_105 (* 3 _for_it_23) 3) (* ncldtop 3)))))
            (not (= tmp_parfor_55_0 tmp_parfor_55_1))
          )
          (not (= tmp_parfor_55_0 tmp_parfor_55_1))
          (or
            (not (= tmp_parfor_55_0 tmp_parfor_55_1))
            (not (= (select _for_it_105_norm_val (- (+ _for_it_105 (* 3 _for_it_23) 3) (* ncldtop 3))) (+ _for_it_106 1)))
          )
        )
        (not (<= tmp_parfor_55_1 (+ kfdia (- 1))))
        (not (<= (+ kidia (- 1)) tmp_parfor_55_1))
        (not (<= tmp_parfor_55_0 (+ kfdia (- 1))))
      )
    )
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= (+ _for_it_106 1) 4)
      (<= (+ (select _for_it_105_norm_val (- (+ (* 3 _for_it_23) (+ _for_it_105 3)) (* ncldtop 3))) 2) 4)
      (<= ncldtop (+ klev (- 1)))
      (<= (+ (select _for_it_105_norm_val (- (+ (* 3 _for_it_23) (+ _for_it_105 3)) (* ncldtop 3))) 1) _for_it_106)
    )
  )
))

(check-sat)