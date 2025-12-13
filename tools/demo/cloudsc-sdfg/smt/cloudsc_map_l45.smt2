

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_22 Int))
  (=>
    (and
      (<= 0 tmp_parfor_22)
      (not (= tmp_parfor_22 (+ tmp_parfor_22 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_22 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)