(declare-fun _for_it_100 () Int)
(declare-fun _for_it_99 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_52 () Int)

(assert (and
  (or
    (not (= tmp_parfor_52 (+ tmp_parfor_52 1)))
    (not (= _for_it_99 _for_it_100))
  )
  (or
    (not (= _for_it_100 _for_it_99))
    (not (= tmp_parfor_52 (+ tmp_parfor_52 1)))
  )
  (not (= tmp_parfor_52 (+ tmp_parfor_52 1)))
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_52 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) tmp_parfor_52)
  )
))

(check-sat)