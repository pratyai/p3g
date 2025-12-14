(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_1 () Int)

(assert (and
  (not (= tmp_parfor_1 (+ tmp_parfor_1 1)))
  (and
    (<= 1 klev)
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_1)
    (<= (+ tmp_parfor_1 1) (+ klon (- 1)))
  )
))

(check-sat)