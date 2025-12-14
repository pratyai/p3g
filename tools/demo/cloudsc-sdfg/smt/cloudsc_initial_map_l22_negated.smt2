(declare-fun klon () Int)
(declare-fun tmp_parfor_11 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= (+ tmp_parfor_11 1) (+ klon (- 1)))
    (<= 0 tmp_parfor_11)
  )
  (not (= tmp_parfor_11 (+ tmp_parfor_11 1)))
))

(check-sat)