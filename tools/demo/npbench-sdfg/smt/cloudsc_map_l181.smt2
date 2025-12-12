

(assert (forall ((_for_it_128 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (= _for_it_128 (+ _for_it_128 1)))
      (<= kidia (+ kfdia (- 1)))
      (<= 1 klev)
      (<= (+ _for_it_128 1) (+ kfdia (- 1)))
      (<= (+ kidia (- 1)) _for_it_128)
    )
    false
  )
))

(check-sat)