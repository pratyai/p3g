(declare-fun _for_it_35 () Int)

(assert (forall ((_for_it_36 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_36 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_36)
      (not (or (= _for_it_36 (+ _for_it_36 1)) (and (= _for_it_36 (+ _for_it_36 1)) (= 4 _for_it_35)) (and (= _for_it_36 (+ _for_it_36 1)) (= _for_it_35 4)) (and (= _for_it_36 (+ _for_it_36 1)) (= 4 _for_it_35) (= _for_it_35 4))))
    )
    false
  )
))

(check-sat)