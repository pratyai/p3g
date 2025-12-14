(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun tmp_parfor_7 () Int)

(assert (and
  (not (= tmp_parfor_7 (+ tmp_parfor_7 1)))
  (and
    (<= (+ tmp_parfor_7 1) (+ klon (- 1)))
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_7)
    (<= 1 (+ klev (- 1)))
  )
))

(check-sat)