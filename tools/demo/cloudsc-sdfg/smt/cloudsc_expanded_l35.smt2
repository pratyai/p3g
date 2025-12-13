

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_15 Int))
  (=>
    (and
      (not (= tmp_parfor_15 (+ tmp_parfor_15 1)))
      (<= 0 tmp_parfor_15)
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_15 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)