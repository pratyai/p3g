

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_16 Int))
  (=>
    (and
      (not (= tmp_parfor_16 (+ tmp_parfor_16 1)))
      (<= 0 tmp_parfor_16)
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_16 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)