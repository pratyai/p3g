(declare-fun _for_it_125 () Int)

(assert (forall ((_for_it_126 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (= _for_it_126 (+ _for_it_126 1)) (and (= _for_it_126 (+ _for_it_126 1)) (= (+ _for_it_125 1) _for_it_125)) (= (- (+ (* _for_it_125 (- kfdia kidia)) _for_it_126 1) kidia) (- (+ (* _for_it_125 (- kfdia kidia)) _for_it_126 2) kidia)) (and (= _for_it_126 (+ _for_it_126 1)) (= _for_it_125 (+ _for_it_125 1)))))
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_126 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_126)
    )
    false
  )
))

(check-sat)