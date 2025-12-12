(declare-fun _for_it_87 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_87 (+ _for_it_87 1)))
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= 0 _for_it_87)
    (<= kidia (+ kfdia (- 1)))
    (<= (+ _for_it_87 1) 4)
  )
))

(check-sat)