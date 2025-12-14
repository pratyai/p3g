(declare-fun _if_cond_0_val () (Array Int Int))

(assert (forall ((_for_it_5 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_5)
      (<= (+ _for_it_5 1) 4)
      (not (or (and (= (select _if_cond_0_val (+ _for_it_5 1)) 1) (= (select _if_cond_0_val _for_it_5) 1) (= _for_it_5 (+ _for_it_5 1))) (= _for_it_5 (+ _for_it_5 1))))
    )
    false
  )
))

(check-sat)