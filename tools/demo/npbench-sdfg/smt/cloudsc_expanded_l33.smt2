

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_13 Int))
  (=>
    (and
      (<= 0 tmp_parfor_13)
      (not (= tmp_parfor_13 (+ tmp_parfor_13 1)))
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_13 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)