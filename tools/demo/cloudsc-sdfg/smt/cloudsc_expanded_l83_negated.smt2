(declare-fun _for_it_35 () Int)
(declare-fun _for_it_36 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (or
    (not (= _for_it_35 4))
    (not (= _for_it_36 (+ _for_it_36 1)))
    (not (= 4 _for_it_35))
  )
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_36 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_36)
    (<= kidia (+ kfdia (- 1)))
  )
  (not (= _for_it_36 (+ _for_it_36 1)))
  (or
    (not (= _for_it_35 4))
    (not (= _for_it_36 (+ _for_it_36 1)))
  )
  (or
    (not (= _for_it_36 (+ _for_it_36 1)))
    (not (= 4 _for_it_35))
  )
))

(check-sat)