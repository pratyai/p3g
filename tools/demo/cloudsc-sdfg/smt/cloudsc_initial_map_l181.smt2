

(assert (forall ((_for_it_128 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= kidia (+ kfdia (- 1)))
      (<= 1 klev)
      (<= (+ _for_it_128 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_128)
      (not (= _for_it_128 (+ _for_it_128 1)))
    )
    false
  )
))

(check-sat)