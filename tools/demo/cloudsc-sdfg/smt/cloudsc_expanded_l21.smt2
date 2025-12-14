

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_10 Int))
  (=>
    (and
      (<= 1 (+ klon (- 1)))
      (<= (+ tmp_parfor_10 1) (+ klon (- 1)))
      (not (= tmp_parfor_10 (+ tmp_parfor_10 1)))
      (<= 0 tmp_parfor_10)
    )
    false
  )
))

(check-sat)