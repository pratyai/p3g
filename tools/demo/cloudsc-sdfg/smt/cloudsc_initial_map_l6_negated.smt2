(declare-fun _for_it_5 () Int)

(assert (forall ((_if_cond_0_val (Array Int Int)))
  (and
    (not (= _for_it_5 (+ _for_it_5 1)))
    (or
      (not (= (select _if_cond_0_val (+ _for_it_5 1)) 1))
      (not (= (select _if_cond_0_val _for_it_5) 1))
      (not (= _for_it_5 (+ _for_it_5 1)))
    )
    (and
      (<= 0 _for_it_5)
      (<= (+ _for_it_5 1) 4)
    )
  )
))

(check-sat)