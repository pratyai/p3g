(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_50 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_50)
    (<= (+ tmp_parfor_50 1) 4)
  )
  (forall ((tmp_parfor_49_0 Int) (tmp_parfor_49_1 Int))
    (or
      (not (<= tmp_parfor_49_1 (+ klon (- 1))))
      (not (<= tmp_parfor_49_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_49_0))
      (not (<= 0 tmp_parfor_49_1))
      (not (= tmp_parfor_49_0 tmp_parfor_49_1))
      (not (= tmp_parfor_50 (+ tmp_parfor_50 1)))
    )
  )
))

(check-sat)