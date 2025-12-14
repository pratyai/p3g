(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_2 () Int)

(assert (and
  (forall ((tmp_parfor_1_0 Int) (tmp_parfor_1_1 Int))
    (or
      (not (<= 0 tmp_parfor_1_0))
      (not (<= 0 tmp_parfor_1_1))
      (not (= tmp_parfor_1_0 tmp_parfor_1_1))
      (not (= tmp_parfor_2 (+ tmp_parfor_2 1)))
      (not (<= tmp_parfor_1_1 (+ klon (- 1))))
      (not (<= tmp_parfor_1_0 (+ klon (- 1))))
    )
  )
  (and
    (<= (+ tmp_parfor_2 1) klev)
    (<= 1 (+ klon (- 1)))
    (<= 1 klev)
    (<= 0 tmp_parfor_2)
  )
))

(check-sat)