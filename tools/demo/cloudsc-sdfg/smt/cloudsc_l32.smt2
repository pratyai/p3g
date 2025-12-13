

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_12 Int))
  (=>
    (and
      (not (= tmp_parfor_12 (+ tmp_parfor_12 1)))
      (<= 0 tmp_parfor_12)
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_12 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)