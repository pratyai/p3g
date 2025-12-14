(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_8 () Int)

(assert (and
  (forall ((tmp_parfor_7_0 Int) (tmp_parfor_7_1 Int))
    (or
      (not (<= 0 tmp_parfor_7_0))
      (not (<= 0 tmp_parfor_7_1))
      (not (= tmp_parfor_7_0 tmp_parfor_7_1))
      (not (= tmp_parfor_8 (+ tmp_parfor_8 1)))
      (not (<= tmp_parfor_7_1 (+ klon (- 1))))
      (not (<= tmp_parfor_7_0 (+ klon (- 1))))
    )
  )
  (and
    (<= (+ tmp_parfor_8 1) (+ klev (- 1)))
    (<= 1 (+ klon (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= 0 tmp_parfor_8)
  )
))

(check-sat)