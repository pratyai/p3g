(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_6 () Int)

(assert (and
  (forall ((tmp_parfor_4_0 Int) (tmp_parfor_4_1 Int) (tmp_parfor_5_0 Int) (tmp_parfor_5_1 Int))
    (or
      (not (<= tmp_parfor_4_1 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_5_0))
      (not (<= tmp_parfor_5_1 (+ klev (- 1))))
      (not (<= 0 tmp_parfor_4_0))
      (not (<= tmp_parfor_4_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_5_1))
      (not (<= tmp_parfor_5_0 (+ klev (- 1))))
      (not (<= 0 tmp_parfor_4_1))
      (not (= tmp_parfor_4_0 tmp_parfor_4_1))
      (not (= tmp_parfor_5_0 tmp_parfor_5_1))
      (not (= tmp_parfor_6 (+ tmp_parfor_6 1)))
    )
  )
  (and
    (<= (+ tmp_parfor_6 1) 4)
    (<= 1 (+ klon (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= 0 tmp_parfor_6)
  )
))

(check-sat)