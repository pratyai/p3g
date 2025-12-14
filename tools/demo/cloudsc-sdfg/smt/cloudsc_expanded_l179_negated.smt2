(declare-fun _for_it_125 () Int)
(declare-fun _for_it_126 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)

(assert (and
  (or
    (not (= (+ _for_it_125 1) _for_it_125))
    (not (= _for_it_126 (+ _for_it_126 1)))
  )
  (or
    (not (= _for_it_126 (+ _for_it_126 1)))
    (not (= (+ _for_it_125 1) _for_it_125))
  )
  (not (= (- (+ _for_it_126 (* _for_it_125 (- kfdia kidia)) 1) kidia) (- (+ _for_it_126 (* _for_it_125 (- kfdia kidia)) 2) kidia)))
  (not (= _for_it_126 (+ _for_it_126 1)))
  (and
    (<= (+ kidia (- 1)) _for_it_126)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ klev (- 1)))
    (<= (+ _for_it_126 1) (+ kfdia (- 1)))
  )
  (or
    (not (= _for_it_125 (+ _for_it_125 1)))
    (not (= _for_it_126 (+ _for_it_126 1)))
  )
))

(check-sat)