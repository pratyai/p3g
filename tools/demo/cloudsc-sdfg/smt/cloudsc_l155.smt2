

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_54 Int))
  (=>
    (and
      (<= (+ kidia (- 1)) tmp_parfor_54)
      (not (= tmp_parfor_54 (+ tmp_parfor_54 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_54 1) (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)