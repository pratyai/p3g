

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_5 Int))
  (=>
    (and
      (<= 0 tmp_parfor_5)
      (<= 1 (+ klon (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ tmp_parfor_5 1) (+ klev (- 1)))
      (not (exists ((tmp_parfor_4_1 Int)(tmp_parfor_4_0 Int)) (and (<= tmp_parfor_4_1 (+ klon (- 1))) (<= tmp_parfor_4_0 (+ klon (- 1))) (<= 0 tmp_parfor_4_0) (<= 0 tmp_parfor_4_1) (= tmp_parfor_4_0 tmp_parfor_4_1) (= tmp_parfor_5 (+ tmp_parfor_5 1)))))
    )
    false
  )
))

(check-sat)