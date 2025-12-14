(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_40 () Int)

(assert (and
  (forall ((tmp_parfor_39_0 Int) (tmp_parfor_39_1 Int))
    (or
      (not (<= 0 tmp_parfor_39_0))
      (not (<= 0 tmp_parfor_39_1))
      (not (= tmp_parfor_39_0 tmp_parfor_39_1))
      (not (= tmp_parfor_40 (+ tmp_parfor_40 1)))
      (not (<= tmp_parfor_39_1 (+ klon (- 1))))
      (not (<= tmp_parfor_39_0 (+ klon (- 1))))
    )
  )
  (and
    (<= (+ tmp_parfor_40 1) 4)
    (<= 1 (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_40)
  )
))

(check-sat)