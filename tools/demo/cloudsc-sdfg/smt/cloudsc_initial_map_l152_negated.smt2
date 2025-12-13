(declare-fun _for_it_103 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((_for_it_104_0 Int) (_for_it_104_1 Int) (tmp_parfor_53_0 Int) (tmp_parfor_53_1 Int))
    (or
      (not (<= tmp_parfor_53_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_53_1))
      (not (<= _for_it_104_1 _for_it_103))
      (not (<= tmp_parfor_53_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_53_0))
      (not (<= _for_it_104_0 (+ _for_it_103 (- 1))))
      (not (<= 0 _for_it_104_0))
      (not (<= 0 _for_it_104_1))
      (and
        (or
          (not (= tmp_parfor_53_0 tmp_parfor_53_1))
          (not (= _for_it_103 (+ _for_it_103 1)))
        )
        (or
          (not (= _for_it_103 _for_it_104_1))
          (not (= tmp_parfor_53_0 tmp_parfor_53_1))
        )
        (or
          (not (= tmp_parfor_53_0 tmp_parfor_53_1))
          (not (= _for_it_104_0 (+ _for_it_103 1)))
        )
      )
    )
  )
  (and
    (<= 1 _for_it_103)
    (<= (+ _for_it_103 1) 4)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ _for_it_103 (- 1)))
    (<= ncldtop (+ klev (- 1)))
  )
))

(check-sat)