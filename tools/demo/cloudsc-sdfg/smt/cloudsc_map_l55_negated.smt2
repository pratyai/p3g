(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_34 () Int)

(assert (and
  (forall ((tmp_parfor_33_0 Int) (tmp_parfor_33_1 Int))
    (or
      (not (<= tmp_parfor_33_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_33_0))
      (not (<= 0 tmp_parfor_33_1))
      (not (= tmp_parfor_33_0 tmp_parfor_33_1))
      (not (= tmp_parfor_34 (+ tmp_parfor_34 1)))
      (not (<= tmp_parfor_33_1 (+ klon (- 1))))
    )
  )
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_34)
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_34 1) 4)
  )
))

(check-sat)