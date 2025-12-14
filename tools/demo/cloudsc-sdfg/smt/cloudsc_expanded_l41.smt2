

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_18 Int))
  (=>
    (and
      (not (= tmp_parfor_18 (+ tmp_parfor_18 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_18 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_18)
    )
    false
  )
))

(check-sat)