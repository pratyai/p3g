

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_27 Int))
  (=>
    (and
      (not (= tmp_parfor_27 (+ tmp_parfor_27 1)))
      (<= 1 (+ klon (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_27 1) (+ klon (- 1)))
      (<= 0 tmp_parfor_27)
    )
    false
  )
))

(check-sat)