(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_3 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_3)
    (<= (+ tmp_parfor_3 1) 4)
    (<= 1 klev)
  )
  (forall ((tmp_parfor_1_0 Int) (tmp_parfor_1_1 Int) (tmp_parfor_2_0 Int) (tmp_parfor_2_1 Int))
    (or
      (not (<= tmp_parfor_1_1 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_2_0))
      (not (<= tmp_parfor_2_0 klev))
      (not (<= tmp_parfor_1_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_1_0))
      (not (<= 0 tmp_parfor_2_1))
      (not (<= tmp_parfor_2_1 klev))
      (not (<= 0 tmp_parfor_1_1))
      (not (= tmp_parfor_1_0 tmp_parfor_1_1))
      (not (= tmp_parfor_2_0 tmp_parfor_2_1))
      (not (= tmp_parfor_3 (+ tmp_parfor_3 1)))
    )
  )
))

(check-sat)