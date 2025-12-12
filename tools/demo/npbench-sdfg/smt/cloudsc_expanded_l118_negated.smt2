(declare-fun _for_it_71 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (not (= _for_it_71 (+ _for_it_71 1)))
  (and
    (<= (+ _for_it_71 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_71)
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
  )
))

(check-sat)