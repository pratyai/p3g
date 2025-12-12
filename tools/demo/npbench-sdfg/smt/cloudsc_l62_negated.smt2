(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_42 () Int)

(assert (and
  (forall ((tmp_parfor_41_0 Int) (tmp_parfor_41_1 Int))
    (or
      (not (<= tmp_parfor_41_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_41_0))
      (not (<= 0 tmp_parfor_41_1))
      (not (= tmp_parfor_41_0 tmp_parfor_41_1))
      (not (= tmp_parfor_42 (+ tmp_parfor_42 1)))
      (not (<= tmp_parfor_41_1 (+ klon (- 1))))
    )
  )
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_42)
    (<= (+ tmp_parfor_42 1) 4)
    (<= 1 (+ klon (- 1)))
  )
))

(check-sat)