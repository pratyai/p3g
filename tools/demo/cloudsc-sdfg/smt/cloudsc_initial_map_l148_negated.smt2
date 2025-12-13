(declare-fun _for_it_100 () Int)
(declare-fun _for_it_99 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (and
    (<= kidia (+ kfdia (- 1)))
    (<= (+ _for_it_99 2) 4)
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_100 1) 4)
    (<= (+ _for_it_99 1) _for_it_100)
  )
  (forall ((_for_it_101_1 Int) (_for_it_102_1 Int) (tmp_parfor_52_0 Int))
    (or
      (and
        (or
          (not (= _for_it_100 _for_it_99))
          (not (= tmp_parfor_52_0 _for_it_102_1))
          (not (= _for_it_99 _for_it_101_1))
        )
        (or
          (not (= tmp_parfor_52_0 _for_it_102_1))
          (not (= _for_it_100 (+ _for_it_100 1)))
        )
        (or
          (not (= tmp_parfor_52_0 _for_it_102_1))
          (not (= _for_it_99 _for_it_101_1))
          (not (= _for_it_99 (+ _for_it_100 1)))
        )
        (or
          (not (= tmp_parfor_52_0 _for_it_102_1))
          (not (= _for_it_99 _for_it_101_1))
          (not (= _for_it_100 (+ _for_it_100 1)))
        )
      )
      (not (<= _for_it_101_1 4))
      (not (<= _for_it_102_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_102_1))
      (not (<= (+ _for_it_99 1) _for_it_101_1))
      (not (<= tmp_parfor_52_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_52_0))
    )
  )
  (forall ((tmp_parfor_52_0 Int) (tmp_parfor_52_1 Int))
    (or
      (and
        (or
          (not (= _for_it_100 _for_it_99))
          (not (= tmp_parfor_52_0 tmp_parfor_52_1))
        )
        (or
          (not (= tmp_parfor_52_0 tmp_parfor_52_1))
          (not (= _for_it_99 (+ _for_it_100 1)))
        )
        (or
          (not (= tmp_parfor_52_0 tmp_parfor_52_1))
          (not (= _for_it_100 (+ _for_it_100 1)))
        )
      )
      (not (<= tmp_parfor_52_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_52_1))
      (not (<= tmp_parfor_52_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_52_0))
    )
  )
  (forall ((_for_it_101_0 Int) (_for_it_101_1 Int) (_for_it_102_0 Int) (_for_it_102_1 Int))
    (or
      (not (<= _for_it_101_0 4))
      (and
        (or
          (not (= _for_it_100 _for_it_99))
          (not (= _for_it_101_0 _for_it_101_1))
          (not (= _for_it_102_0 _for_it_102_1))
        )
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_100 (+ _for_it_100 1)))
          (not (= _for_it_101_0 _for_it_99))
        )
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_101_0 _for_it_101_1))
          (not (= _for_it_99 (+ _for_it_100 1)))
        )
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_99 _for_it_101_1))
          (not (= _for_it_100 (+ _for_it_100 1)))
        )
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_101_0 _for_it_101_1))
          (not (= _for_it_100 (+ _for_it_100 1)))
        )
      )
      (not (<= _for_it_102_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_102_0))
      (not (<= _for_it_101_1 4))
      (not (<= _for_it_102_1 (+ kfdia (- 1))))
      (not (<= (+ _for_it_99 1) _for_it_101_0))
      (not (<= (+ kidia (- 1)) _for_it_102_1))
      (not (<= (+ _for_it_99 1) _for_it_101_1))
    )
  )
  (forall ((_for_it_101_0 Int) (_for_it_102_0 Int) (tmp_parfor_52_1 Int))
    (or
      (not (<= _for_it_101_0 4))
      (not (<= _for_it_102_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_102_0))
      (not (<= (+ _for_it_99 1) _for_it_101_0))
      (not (<= tmp_parfor_52_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_52_1))
      (and
        (or
          (not (= _for_it_100 (+ _for_it_100 1)))
          (not (= _for_it_102_0 tmp_parfor_52_1))
        )
        (or
          (not (= _for_it_100 (+ _for_it_100 1)))
          (not (= _for_it_102_0 tmp_parfor_52_1))
          (not (= _for_it_101_0 _for_it_99))
        )
        (or
          (not (= _for_it_100 _for_it_99))
          (not (= _for_it_102_0 tmp_parfor_52_1))
          (not (= _for_it_101_0 _for_it_99))
        )
        (or
          (not (= _for_it_99 (+ _for_it_100 1)))
          (not (= _for_it_102_0 tmp_parfor_52_1))
          (not (= _for_it_101_0 _for_it_99))
        )
      )
    )
  )
))

(check-sat)