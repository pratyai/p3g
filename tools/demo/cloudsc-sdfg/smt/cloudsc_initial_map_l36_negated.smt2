(declare-fun klon () Int)
(declare-fun tmp_parfor_16 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= (+ tmp_parfor_16 1) (+ klon (- 1)))
    (<= 0 tmp_parfor_16)
  )
  (not (= tmp_parfor_16 (+ tmp_parfor_16 1)))
))

(check-sat)