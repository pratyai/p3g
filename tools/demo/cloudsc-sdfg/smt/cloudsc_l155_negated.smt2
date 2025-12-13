(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_54 () Int)

(assert (and
  (and
    (<= (+ kidia (- 1)) tmp_parfor_54)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_54 1) (+ kfdia (- 1)))
  )
  (not (= tmp_parfor_54 (+ tmp_parfor_54 1)))
))

(check-sat)