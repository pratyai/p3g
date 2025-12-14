

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_38 Int))
  (=>
    (and
      (not (exists ((tmp_parfor_37_0 Int)(tmp_parfor_37_1 Int)(tmp_parfor_36_0 Int)(tmp_parfor_36_1 Int)) (and (<= tmp_parfor_36_1 (+ klon (- 1))) (<= 0 tmp_parfor_37_0) (<= tmp_parfor_37_0 4) (<= tmp_parfor_36_0 (+ klon (- 1))) (<= 0 tmp_parfor_36_0) (<= 0 tmp_parfor_37_1) (<= tmp_parfor_37_1 4) (<= 0 tmp_parfor_36_1) (= tmp_parfor_36_0 tmp_parfor_36_1) (= tmp_parfor_37_0 tmp_parfor_37_1) (= tmp_parfor_38 (+ tmp_parfor_38 1)))))
      (<= 0 tmp_parfor_38)
      (<= (+ tmp_parfor_38 1) 4)
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)