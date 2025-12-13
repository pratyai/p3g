(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_19 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= (+ tmp_parfor_19 1) (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= 0 tmp_parfor_19)
  )
  (not (= tmp_parfor_19 (+ tmp_parfor_19 1)))
))

(check-sat)