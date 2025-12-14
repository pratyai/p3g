(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_20 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_20 1) (+ klon (- 1)))
    (<= 0 tmp_parfor_20)
  )
  (not (= tmp_parfor_20 (+ tmp_parfor_20 1)))
))

(check-sat)