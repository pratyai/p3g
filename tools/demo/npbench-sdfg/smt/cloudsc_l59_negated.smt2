(declare-fun klev () Int)
(declare-fun klon () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_36 () Int)

(assert (and
  (and
    (<= 1 (+ klon (- 1)))
    (<= 0 tmp_parfor_36)
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_36 1) (+ klon (- 1)))
  )
  (not (= tmp_parfor_36 (+ tmp_parfor_36 1)))
))

(check-sat)