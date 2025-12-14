

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_23 Int))
  (=>
    (and
      (not (= tmp_parfor_23 (+ tmp_parfor_23 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_23 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_23)
    )
    false
  )
))

(check-sat)