

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_25 Int))
  (=>
    (and
      (not (= tmp_parfor_25 (+ tmp_parfor_25 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_25 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_25)
    )
    false
  )
))

(check-sat)