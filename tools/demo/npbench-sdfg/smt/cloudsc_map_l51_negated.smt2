(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_28 () Int)

(assert (and
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_28)
    (<= (+ tmp_parfor_28 1) (+ klon (- 1)))
    (<= 1 (+ klon (- 1)))
  )
  (not (= tmp_parfor_28 (+ tmp_parfor_28 1)))
))

(check-sat)