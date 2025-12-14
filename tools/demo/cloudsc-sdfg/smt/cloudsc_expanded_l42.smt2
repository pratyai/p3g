

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_19 Int))
  (=>
    (and
      (not (= tmp_parfor_19 (+ tmp_parfor_19 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_19 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_19)
    )
    false
  )
))

(check-sat)