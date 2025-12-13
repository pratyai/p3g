

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_51 Int))
  (=>
    (and
      (<= 0 tmp_parfor_51)
      (not (= tmp_parfor_51 (+ tmp_parfor_51 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_51 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)