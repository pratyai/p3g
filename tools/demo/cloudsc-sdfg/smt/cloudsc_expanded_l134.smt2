

(assert (forall ((_for_it_87 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= ncldtop (+ klev (- 1)))
      (<= 0 _for_it_87)
      (<= (+ _for_it_87 1) 4)
      (not (= _for_it_87 (+ _for_it_87 1)))
      (<= kidia (+ kfdia (- 1)))
    )
    false
  )
))

(check-sat)