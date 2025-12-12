

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_2 Int))
  (=>
    (and
      (<= 0 tmp_parfor_2)
      (<= (+ tmp_parfor_2 1) klev)
      (<= 1 (+ klon (- 1)))
      (<= 1 klev)
      (not (exists ((tmp_parfor_1_1 Int)(tmp_parfor_1_0 Int)) (and (<= tmp_parfor_1_0 (+ klon (- 1))) (<= 0 tmp_parfor_1_0) (<= 0 tmp_parfor_1_1) (= tmp_parfor_1_0 tmp_parfor_1_1) (= tmp_parfor_2 (+ tmp_parfor_2 1)) (<= tmp_parfor_1_1 (+ klon (- 1))))))
    )
    false
  )
))

(check-sat)