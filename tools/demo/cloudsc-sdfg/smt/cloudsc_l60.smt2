

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_40 Int))
  (=>
    (and
      (<= 0 tmp_parfor_40)
      (<= (+ tmp_parfor_40 1) 4)
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (not (exists ((tmp_parfor_39_0 Int)(tmp_parfor_39_1 Int)) (and (<= tmp_parfor_39_1 (+ klon (- 1))) (<= tmp_parfor_39_0 (+ klon (- 1))) (<= 0 tmp_parfor_39_0) (<= 0 tmp_parfor_39_1) (= tmp_parfor_39_0 tmp_parfor_39_1) (= tmp_parfor_40 (+ tmp_parfor_40 1)))))
    )
    false
  )
))

(check-sat)