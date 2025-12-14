(declare-fun _for_it_103 () Int)
(declare-fun _for_it_104 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)
(declare-fun tmp_parfor_53 () Int)

(assert (and
  (or
    (not (= _for_it_103 _for_it_104))
    (not (= tmp_parfor_53 (+ tmp_parfor_53 1)))
  )
  (not (= tmp_parfor_53 (+ tmp_parfor_53 1)))
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ tmp_parfor_53 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) tmp_parfor_53)
  )
  (or
    (not (= tmp_parfor_53 (+ tmp_parfor_53 1)))
    (not (= _for_it_104 _for_it_103))
  )
))

(check-sat)