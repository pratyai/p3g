

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_50 Int))
  (=>
    (and
      (<= (+ tmp_parfor_50 1) 4)
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((tmp_parfor_49_0 Int)(tmp_parfor_49_1 Int)) (and (<= 0 tmp_parfor_49_0) (<= 0 tmp_parfor_49_1) (= tmp_parfor_49_0 tmp_parfor_49_1) (= tmp_parfor_50 (+ tmp_parfor_50 1)) (<= tmp_parfor_49_1 (+ klon (- 1))) (<= tmp_parfor_49_0 (+ klon (- 1))))))
      (<= 0 tmp_parfor_50)
    )
    false
  )
))

(check-sat)