

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_43 Int))
  (=>
    (and
      (not (= tmp_parfor_43 (+ tmp_parfor_43 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_43 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_43)
    )
    false
  )
))

(check-sat)