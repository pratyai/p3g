(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_44 () Int)

(assert (and
  (forall ((tmp_parfor_43_0 Int) (tmp_parfor_43_1 Int))
    (or
      (not (<= 0 tmp_parfor_43_0))
      (not (<= 0 tmp_parfor_43_1))
      (not (= tmp_parfor_43_0 tmp_parfor_43_1))
      (not (= tmp_parfor_44 (+ tmp_parfor_44 1)))
      (not (<= tmp_parfor_43_1 (+ klon (- 1))))
      (not (<= tmp_parfor_43_0 (+ klon (- 1))))
    )
  )
  (and
    (<= (+ tmp_parfor_44 1) 4)
    (<= 1 (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_44)
  )
))

(check-sat)