(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_33 () Int)

(assert (and
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_33 1) (+ klon (- 1)))
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_33)
  )
  (not (= tmp_parfor_33 (+ tmp_parfor_33 1)))
))

(check-sat)