(declare-fun ptare_var_0_val () (Array Int Int))
(declare-fun rtt () Int)

(assert (forall ((_for_it_16 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_16)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_16 1) (+ klev (- 1)))
      (not (or (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1))) (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0) (= _for_it_17_0 _for_it_17_1) (= _for_it_16 (+ _for_it_16 1)) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1))) (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0) (<= rtt (select ptare_var_0_val 0)) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1))) (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0) (not (<= rtt (select ptare_var_0_val 0))) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1)))))
    )
    false
  )
))

(check-sat)