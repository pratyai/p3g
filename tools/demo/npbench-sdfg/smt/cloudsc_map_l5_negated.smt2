(declare-fun tmp_parfor_0 () Int)

(assert (and
  (not (= tmp_parfor_0 (+ tmp_parfor_0 1)))
  (and
    (<= 0 tmp_parfor_0)
    (<= (+ tmp_parfor_0 1) 4)
  )
))

(check-sat)