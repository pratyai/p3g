(declare-fun _for_it_103 () Int)
(declare-fun _for_it_104 () Int)

(assert (forall ((kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int) (tmp_parfor_53 Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ tmp_parfor_53 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) tmp_parfor_53)
      (not (or (and (= _for_it_103 _for_it_104) (= tmp_parfor_53 (+ tmp_parfor_53 1))) (= tmp_parfor_53 (+ tmp_parfor_53 1)) (and (= tmp_parfor_53 (+ tmp_parfor_53 1)) (= _for_it_104 _for_it_103))))
    )
    false
  )
))

(check-sat)