(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_56 () Int)

(assert (and
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_56 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) tmp_parfor_56)
    (<= kidia (+ kfdia (- 1)))
  )
  (not (= tmp_parfor_56 (+ tmp_parfor_56 1)))
))

(check-sat)