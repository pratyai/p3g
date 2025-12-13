

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_45 Int))
  (=>
    (and
      (<= 0 tmp_parfor_45)
      (not (= tmp_parfor_45 (+ tmp_parfor_45 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_45 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)