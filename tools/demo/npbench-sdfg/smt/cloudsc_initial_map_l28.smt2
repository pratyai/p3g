(declare-fun ptare_var_0 () Int)
(declare-fun rtt_var_1 () Int)

(assert (forall ((_for_it_16 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (<= 0 _for_it_16)
      (<= kidia (+ kfdia (- 1)))
      (<= 1 (+ klev (- 1)))
      (<= (+ _for_it_16 1) (+ klev (- 1)))
      (not (or (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (= _for_it_17_0 _for_it_17_1) (= _for_it_16 (+ _for_it_16 1)) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1) (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0))) (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (<= (+ kidia (- 1)) _for_it_17_1) (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0) (<= _for_it_17_1 (+ kfdia (- 1))))) (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (<= rtt_var_1 ptare_var_0) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1) (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0))) (exists ((_for_it_17_0 Int)(_for_it_17_1 Int)) (and (not (<= rtt_var_1 ptare_var_0)) (<= _for_it_17_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_1) (<= _for_it_17_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_17_0)))))
    )
    false
  )
))

(check-sat)