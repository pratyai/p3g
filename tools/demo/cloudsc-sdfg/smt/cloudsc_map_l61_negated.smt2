(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_39 () Int)

(assert (and
  (not (= tmp_parfor_39 (+ tmp_parfor_39 1)))
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_39 1) (+ klon (- 1)))
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_39)
  )
))

(check-sat)