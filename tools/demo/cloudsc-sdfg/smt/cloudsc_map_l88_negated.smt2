(declare-fun _for_it_23 () Int)
(declare-fun _for_it_41 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (or
    (not (< (+ _for_it_23 1) klev))
    (not (= _for_it_41 0))
  )
  (not (= _for_it_41 (+ _for_it_41 1)))
  (not (< (+ _for_it_23 1) klev))
  (or
    (not (< (+ _for_it_23 1) klev))
    (not (= 0 (+ _for_it_41 1)))
  )
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_41 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_41)
    (<= kidia (+ kfdia (- 1)))
  )
))

(check-sat)