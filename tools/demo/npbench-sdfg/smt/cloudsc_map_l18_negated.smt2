(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_9 () Int)

(assert (and
  (forall ((tmp_parfor_7_0 Int) (tmp_parfor_7_1 Int) (tmp_parfor_8_0 Int) (tmp_parfor_8_1 Int))
    (or
      (not (<= tmp_parfor_7_1 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_8_0))
      (not (<= tmp_parfor_8_1 (+ klev (- 1))))
      (not (<= 0 tmp_parfor_7_0))
      (not (<= tmp_parfor_7_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_8_1))
      (not (<= tmp_parfor_8_0 (+ klev (- 1))))
      (not (<= 0 tmp_parfor_7_1))
      (not (= tmp_parfor_7_0 tmp_parfor_7_1))
      (not (= tmp_parfor_8_0 tmp_parfor_8_1))
      (not (= tmp_parfor_9 (+ tmp_parfor_9 1)))
    )
  )
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_9)
    (<= (+ tmp_parfor_9 1) 4)
    (<= 1 (+ klev (- 1)))
  )
))

(check-sat)