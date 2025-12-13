

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_0 Int))
  (=>
    (and
      (not (= tmp_parfor_0 (+ tmp_parfor_0 1)))
      (<= 0 tmp_parfor_0)
      (<= (+ tmp_parfor_0 1) 4)
    )
    false
  )
))

(check-sat)