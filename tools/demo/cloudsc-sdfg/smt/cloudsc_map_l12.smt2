

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_3 Int))
  (=>
    (and
      (not (exists ((tmp_parfor_2_1 Int)(tmp_parfor_1_0 Int)(tmp_parfor_1_1 Int)(tmp_parfor_2_0 Int)) (and (= tmp_parfor_1_0 tmp_parfor_1_1) (= tmp_parfor_2_0 tmp_parfor_2_1) (= tmp_parfor_3 (+ tmp_parfor_3 1)) (<= tmp_parfor_1_1 (+ klon (- 1))) (<= 0 tmp_parfor_2_0) (<= tmp_parfor_2_0 klev) (<= tmp_parfor_1_0 (+ klon (- 1))) (<= 0 tmp_parfor_1_0) (<= 0 tmp_parfor_2_1) (<= tmp_parfor_2_1 klev) (<= 0 tmp_parfor_1_1))))
      (<= 0 tmp_parfor_3)
      (<= (+ tmp_parfor_3 1) 4)
      (<= 1 (+ klon (- 1)))
      (<= 1 klev)
    )
    false
  )
))

(check-sat)