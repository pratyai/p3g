(declare-fun tmp_parfor_0 () Int)

(assert (and
  (and
    (<= 0 tmp_parfor_0)
    (<= (+ tmp_parfor_0 1) 4)
  )
  (not (= tmp_parfor_0 (+ tmp_parfor_0 1)))
))

(check-sat)