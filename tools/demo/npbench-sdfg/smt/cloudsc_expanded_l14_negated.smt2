(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_1 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_1)
    (<= (+ tmp_parfor_1 1) (+ klon (- 1)))
    (<= 1 klev)
  )
  (not (= tmp_parfor_1 (+ tmp_parfor_1 1)))
))

(check-sat)