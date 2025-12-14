

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_39 Int))
  (=>
    (and
      (not (= tmp_parfor_39 (+ tmp_parfor_39 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_39 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_39)
    )
    false
  )
))

(check-sat)