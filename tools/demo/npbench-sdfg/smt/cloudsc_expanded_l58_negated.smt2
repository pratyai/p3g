(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_37 () Int)

(assert (and
  (forall ((tmp_parfor_36_0 Int) (tmp_parfor_36_1 Int))
    (or
      (not (<= tmp_parfor_36_0 (+ klon (- 1))))
      (not (<= 0 tmp_parfor_36_0))
      (not (<= 0 tmp_parfor_36_1))
      (not (= tmp_parfor_36_0 tmp_parfor_36_1))
      (not (= tmp_parfor_37 (+ tmp_parfor_37 1)))
      (not (<= tmp_parfor_36_1 (+ klon (- 1))))
    )
  )
  (and
    (<= 1 (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_37)
    (<= (+ tmp_parfor_37 1) 4)
  )
))

(check-sat)