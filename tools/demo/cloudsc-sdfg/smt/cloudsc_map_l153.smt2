

(assert (forall ((_for_it_103 Int) (_for_it_104 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ _for_it_103 (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_104 1) (+ _for_it_103 (- 1)))
      (<= 0 _for_it_104)
      (not (exists ((tmp_parfor_53_1 Int)(tmp_parfor_53_0 Int)) (and (or (and (= _for_it_103 (+ _for_it_104 1)) (= tmp_parfor_53_0 tmp_parfor_53_1)) (= tmp_parfor_53_0 tmp_parfor_53_1) (and (= tmp_parfor_53_0 tmp_parfor_53_1) (= _for_it_104 _for_it_103))) (<= tmp_parfor_53_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_53_1) (<= tmp_parfor_53_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_53_0))))
    )
    false
  )
))

(check-sat)