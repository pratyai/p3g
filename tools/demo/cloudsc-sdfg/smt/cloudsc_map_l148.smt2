

(assert (forall ((_for_it_100 Int) (_for_it_99 Int) (kfdia Int) (kidia Int) (klev Int) (klon Int) (ncldtop Int))
  (=>
    (and
      (not (or (exists ((_for_it_101_1 Int)(_for_it_101_0 Int)(_for_it_102_1 Int)(_for_it_102_0 Int)) (and (<= _for_it_102_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_102_0) (<= _for_it_101_1 4) (<= _for_it_102_1 (+ kfdia (- 1))) (<= (+ _for_it_99 1) _for_it_101_0) (<= (+ kidia (- 1)) _for_it_102_1) (<= (+ _for_it_99 1) _for_it_101_1) (<= _for_it_101_0 4) (or (and (= _for_it_102_0 _for_it_102_1) (= _for_it_100 (+ _for_it_100 1)) (= _for_it_101_0 _for_it_99)) (and (= _for_it_102_0 _for_it_102_1) (= _for_it_101_0 _for_it_101_1) (= _for_it_99 (+ _for_it_100 1))) (and (= _for_it_102_0 _for_it_102_1) (= _for_it_99 _for_it_101_1) (= _for_it_100 (+ _for_it_100 1))) (and (= _for_it_102_0 _for_it_102_1) (= _for_it_101_0 _for_it_101_1) (= _for_it_100 (+ _for_it_100 1))) (and (= _for_it_102_0 _for_it_102_1) (= _for_it_101_0 _for_it_101_1) (= _for_it_100 _for_it_99))))) (exists ((tmp_parfor_52_1 Int)(tmp_parfor_52_0 Int)) (and (or (and (= _for_it_100 _for_it_99) (= tmp_parfor_52_0 tmp_parfor_52_1)) (and (= tmp_parfor_52_0 tmp_parfor_52_1) (= _for_it_99 (+ _for_it_100 1))) (and (= tmp_parfor_52_0 tmp_parfor_52_1) (= _for_it_100 (+ _for_it_100 1)))) (<= tmp_parfor_52_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_52_1) (<= tmp_parfor_52_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_52_0))) (exists ((_for_it_101_1 Int)(tmp_parfor_52_0 Int)(_for_it_102_1 Int)) (and (<= _for_it_101_1 4) (or (and (= tmp_parfor_52_0 _for_it_102_1) (= _for_it_99 _for_it_101_1) (= _for_it_100 _for_it_99)) (and (= tmp_parfor_52_0 _for_it_102_1) (= _for_it_100 (+ _for_it_100 1))) (and (= tmp_parfor_52_0 _for_it_102_1) (= _for_it_99 _for_it_101_1) (= _for_it_99 (+ _for_it_100 1))) (and (= tmp_parfor_52_0 _for_it_102_1) (= _for_it_99 _for_it_101_1) (= _for_it_100 (+ _for_it_100 1)))) (<= _for_it_102_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_102_1) (<= (+ _for_it_99 1) _for_it_101_1) (<= tmp_parfor_52_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_52_0))) (exists ((tmp_parfor_52_1 Int)(_for_it_102_0 Int)(_for_it_101_0 Int)) (and (or (and (= _for_it_100 (+ _for_it_100 1)) (= _for_it_102_0 tmp_parfor_52_1)) (and (= _for_it_100 (+ _for_it_100 1)) (= _for_it_102_0 tmp_parfor_52_1) (= _for_it_101_0 _for_it_99)) (and (= _for_it_100 _for_it_99) (= _for_it_102_0 tmp_parfor_52_1) (= _for_it_101_0 _for_it_99)) (and (= _for_it_102_0 tmp_parfor_52_1) (= _for_it_99 (+ _for_it_100 1)) (= _for_it_101_0 _for_it_99))) (<= _for_it_102_0 (+ kfdia (- 1))) (<= (+ kidia (- 1)) _for_it_102_0) (<= (+ _for_it_99 1) _for_it_101_0) (<= tmp_parfor_52_1 (+ kfdia (- 1))) (<= (+ kidia (- 1)) tmp_parfor_52_1) (<= _for_it_101_0 4)))))
      (<= kidia (+ kfdia (- 1)))
      (<= (+ _for_it_99 2) 4)
      (<= ncldtop (+ klev (- 1)))
      (<= (+ _for_it_99 1) _for_it_100)
      (<= (+ _for_it_100 1) 4)
    )
    false
  )
))

(check-sat)