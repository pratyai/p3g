

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_33 Int))
  (=>
    (and
      (not (= tmp_parfor_33 (+ tmp_parfor_33 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_33 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_33)
    )
    false
  )
))

(check-sat)