

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_0 Int))
  (=>
    (and
      (<= 0 tmp_parfor_0)
      (<= (+ tmp_parfor_0 1) 4)
      (not (= tmp_parfor_0 (+ tmp_parfor_0 1)))
    )
    false
  )
))

(check-sat)