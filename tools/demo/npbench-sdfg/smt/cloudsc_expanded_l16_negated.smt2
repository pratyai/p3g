(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_5 () Int)

(assert (and
  (forall ((tmp_parfor_4_0 Int) (tmp_parfor_4_1 Int))
    (or
      (not (<= tmp_parfor_4_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_4_0))
      (not (<= 0 tmp_parfor_4_1))
      (not (= tmp_parfor_4_0 tmp_parfor_4_1))
      (not (= tmp_parfor_5 (+ tmp_parfor_5 1)))
      (not (<= tmp_parfor_4_1 (+ klon (- 1))))
    )
  )
  (and
    (<= 1 (+ klon (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= 0 tmp_parfor_5)
    (<= (+ tmp_parfor_5 1) (+ klev (- 1)))
  )
))

(check-sat)