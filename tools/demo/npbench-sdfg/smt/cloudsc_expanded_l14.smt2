

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_1 Int))
  (=>
    (and
      (<= 0 tmp_parfor_1)
      (not (= tmp_parfor_1 (+ tmp_parfor_1 1)))
      (<= 1 (+ klon (- 1)))
      (<= 1 klev)
      (<= (+ tmp_parfor_1 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)