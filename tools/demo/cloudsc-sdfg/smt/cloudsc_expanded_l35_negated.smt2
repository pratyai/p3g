(declare-fun klon () Int)
(declare-fun tmp_parfor_15 () Int)

(assert (and
  (and
    (<= 0 tmp_parfor_15)
    (<= 1 (+ klon (- 1)))
    (<= (+ tmp_parfor_15 1) (+ klon (- 1)))
  )
  (not (= tmp_parfor_15 (+ tmp_parfor_15 1)))
))

(check-sat)