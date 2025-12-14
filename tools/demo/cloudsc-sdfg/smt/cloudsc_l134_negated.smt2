(declare-fun _for_it_87 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= (+ _for_it_87 1) 4)
    (<= ncldtop (+ klev (- 1)))
    (<= kidia (+ kfdia (- 1)))
    (<= 0 _for_it_87)
  )
  (not (= _for_it_87 (+ _for_it_87 1)))
))

(check-sat)