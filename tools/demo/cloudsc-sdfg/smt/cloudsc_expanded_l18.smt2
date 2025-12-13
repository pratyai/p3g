

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_9 Int))
  (=>
    (and
      (<= 1 (+ klon (- 1)))
      (<= 1 (+ klev (- 1)))
      (not (exists ((tmp_parfor_8_1 Int)(tmp_parfor_7_0 Int)(tmp_parfor_7_1 Int)(tmp_parfor_8_0 Int)) (and (= tmp_parfor_7_0 tmp_parfor_7_1) (= tmp_parfor_8_0 tmp_parfor_8_1) (= tmp_parfor_9 (+ tmp_parfor_9 1)) (<= tmp_parfor_7_1 (+ klon (- 1))) (<= 0 tmp_parfor_8_0) (<= tmp_parfor_8_1 (+ klev (- 1))) (<= 0 tmp_parfor_7_0) (<= tmp_parfor_7_0 (+ klon (- 1))) (<= 0 tmp_parfor_8_1) (<= tmp_parfor_8_0 (+ klev (- 1))) (<= 0 tmp_parfor_7_1))))
      (<= 0 tmp_parfor_9)
      (<= (+ tmp_parfor_9 1) 4)
    )
    false
  )
))

(check-sat)