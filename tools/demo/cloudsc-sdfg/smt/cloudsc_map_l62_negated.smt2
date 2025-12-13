(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_42 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_42)
    (<= (+ tmp_parfor_42 1) 4)
  )
  (forall ((tmp_parfor_41_0 Int) (tmp_parfor_41_1 Int))
    (or
      (not (<= tmp_parfor_41_1 (+ klon (- 1))))
      (not (<= tmp_parfor_41_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_41_0))
      (not (<= 0 tmp_parfor_41_1))
      (not (= tmp_parfor_41_0 tmp_parfor_41_1))
      (not (= tmp_parfor_42 (+ tmp_parfor_42 1)))
    )
  )
))

(check-sat)