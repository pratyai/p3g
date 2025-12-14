

(assert (forall ((_for_it_87 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (= _for_it_87 (+ _for_it_87 1)))
      (<= 0 _for_it_87)
      (<= (+ _for_it_87 1) 4)
      (<= kidia (+ kfdia (- 1)))
      (<= ncldtop (+ klev (- 1)))
    )
    false
  )
))

(check-sat)