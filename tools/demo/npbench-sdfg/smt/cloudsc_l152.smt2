

(assert (forall ((_for_it_103 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (exists ((tmp_parfor_53_0 Int)(tmp_parfor_53_1 Int)(_for_it_104_0 Int)(_for_it_104_1 Int)) (and (<= tmp_parfor_53_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_53_0) (<= _for_it_104_0 (+ _for_it_103 (- 1))) (<= 0 _for_it_104_0) (<= 0 _for_it_104_1) (or (and (= tmp_parfor_53_0 tmp_parfor_53_1) (= _for_it_104_0 (+ _for_it_103 1))) (and (= _for_it_103 _for_it_104_1) (= tmp_parfor_53_0 tmp_parfor_53_1)) (and (= tmp_parfor_53_0 tmp_parfor_53_1) (= _for_it_103 (+ _for_it_103 1)))) (<= tmp_parfor_53_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_53_1) (<= _for_it_104_1 _for_it_103))))
      (<= 1 _for_it_103)
      (<= (+ _for_it_103 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ _for_it_103 (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)