(declare-fun _for_it_100 () Int)
(declare-fun _for_it_101 () Int)
(declare-fun _for_it_102 () Int)
(declare-fun _for_it_99 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (or
    (not (= _for_it_99 _for_it_101))
    (not (= _for_it_102 (+ _for_it_102 1)))
  )
  (not (= _for_it_102 (+ _for_it_102 1)))
  (or
    (not (= _for_it_102 (+ _for_it_102 1)))
    (not (= _for_it_100 _for_it_99))
  )
  (or
    (not (= _for_it_101 _for_it_99))
    (not (= _for_it_102 (+ _for_it_102 1)))
  )
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_102 1) (+ kfdia (- 1)))
    (<= (+ kidia (- 1)) _for_it_102)
  )
  (or
    (not (= _for_it_99 _for_it_100))
    (not (= _for_it_102 (+ _for_it_102 1)))
  )
))

(check-sat)