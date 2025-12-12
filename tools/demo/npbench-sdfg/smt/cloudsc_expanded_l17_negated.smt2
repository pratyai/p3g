(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_4 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_4)
    (<= 1 (+ klev (- 1)))
    (<= (+ tmp_parfor_4 1) (+ klon (- 1)))
  )
  (not (= tmp_parfor_4 (+ tmp_parfor_4 1)))
))

(check-sat)