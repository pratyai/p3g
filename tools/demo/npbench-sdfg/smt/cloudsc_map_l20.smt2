

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_7 Int))
  (=>
    (and
      (<= 0 tmp_parfor_7)
      (not (= tmp_parfor_7 (+ tmp_parfor_7 1)))
      (<= 1 (+ klon (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ tmp_parfor_7 1) (+ klon (- 1)))
    )
    false
  )
))

(check-sat)