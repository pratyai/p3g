(declare-fun klon () Int)
(declare-fun tmp_parfor_14 () Int)

(assert (and
  (and
    (<= 0 tmp_parfor_14)
    (<= 1 (+ klon (- 1)))
    (<= (+ tmp_parfor_14 1) (+ klon (- 1)))
  )
  (not (= tmp_parfor_14 (+ tmp_parfor_14 1)))
))

(check-sat)