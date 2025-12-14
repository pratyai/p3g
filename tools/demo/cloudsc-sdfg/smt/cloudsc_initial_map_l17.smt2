

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_4 Int))
  (=>
    (and
      (not (= tmp_parfor_4 (+ tmp_parfor_4 1)))
      (<= 1 (+ klon (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ tmp_parfor_4 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_4)
    )
    false
  )
))

(check-sat)