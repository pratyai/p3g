(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_43 () Int)

(assert (and
  (not (= tmp_parfor_43 (+ tmp_parfor_43 1)))
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_43)
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_43 1) (+ klon (- 1)))
  )
))

(check-sat)