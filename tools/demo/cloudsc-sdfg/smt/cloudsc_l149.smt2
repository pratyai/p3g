(declare-fun _for_it_100 () Int)
(declare-fun _for_it_99 () Int)

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_52 Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_52 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) tmp_parfor_52)
      (not (or (and (= _for_it_100 _for_it_99) (= tmp_parfor_52 (+ tmp_parfor_52 1))) (= tmp_parfor_52 (+ tmp_parfor_52 1)) (and (= tmp_parfor_52 (+ tmp_parfor_52 1)) (= _for_it_99 _for_it_100))))
    )
    false
  )
))

(check-sat)