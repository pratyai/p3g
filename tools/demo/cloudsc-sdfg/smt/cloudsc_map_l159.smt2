

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_56 Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_56 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) tmp_parfor_56)
      (not (= tmp_parfor_56 (+ tmp_parfor_56 1)))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)