

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_11 Int))
  (=>
    (and
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_11 1) (+ klon (- 1)))
      (not (= tmp_parfor_11 (+ tmp_parfor_11 1)))
      (<= 0 tmp_parfor_11)
    )
    false
  )
))

(check-sat)