

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_34 Int))
  (=>
    (and
      (<= 0 tmp_parfor_34)
      (<= (+ tmp_parfor_34 1) 4)
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((tmp_parfor_33_0 Int)(tmp_parfor_33_1 Int)) (and (<= tmp_parfor_33_1 (+ klon (- 1))) (<= tmp_parfor_33_0 (+ klon (- 1))) (<= 0 tmp_parfor_33_0) (<= 0 tmp_parfor_33_1) (= tmp_parfor_33_0 tmp_parfor_33_1) (= tmp_parfor_34 (+ tmp_parfor_34 1)))))
    )
    false
  )
))

(check-sat)