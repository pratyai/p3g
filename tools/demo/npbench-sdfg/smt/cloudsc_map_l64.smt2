

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_44 Int))
  (=>
    (and
      (<= 0 tmp_parfor_44)
      (<= (+ tmp_parfor_44 1) 4)
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((tmp_parfor_43_1 Int)(tmp_parfor_43_0 Int)) (and (<= tmp_parfor_43_0 (+ klon (- 1))) (<= 0 tmp_parfor_43_0) (<= 0 tmp_parfor_43_1) (= tmp_parfor_43_0 tmp_parfor_43_1) (= tmp_parfor_44 (+ tmp_parfor_44 1)) (<= tmp_parfor_43_1 (+ klon (- 1))))))
    )
    false
  )
))

(check-sat)