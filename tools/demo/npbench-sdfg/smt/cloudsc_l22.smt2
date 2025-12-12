

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_11 Int))
  (=>
    (and
      (<= 0 tmp_parfor_11)
      (not (= tmp_parfor_11 (+ tmp_parfor_11 1)))
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_11 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)