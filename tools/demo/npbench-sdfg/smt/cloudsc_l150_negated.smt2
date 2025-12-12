(declare-fun _for_it_100 () Int)
(declare-fun _for_it_101 () Int)
(declare-fun _for_it_99 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((_for_it_102_0 Int) (_for_it_102_1 Int))
    (or
      (not (<= _for_it_102_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_102_0))
      (and
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_101 (+ _for_it_101 1)))
          (not (= _for_it_99 _for_it_100))
        )
        (or
          (not (= _for_it_99 (+ _for_it_101 1)))
          (not (= _for_it_102_0 _for_it_102_1))
        )
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_101 (+ _for_it_101 1)))
        )
        (or
          (not (= _for_it_101 _for_it_99))
          (not (= _for_it_102_0 _for_it_102_1))
        )
        (or
          (not (= _for_it_102_0 _for_it_102_1))
          (not (= _for_it_100 _for_it_99))
          (not (= _for_it_101 (+ _for_it_101 1)))
        )
      )
      (not (<= _for_it_102_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) _for_it_102_1))
    )
  )
  (and
    (<= (+ _for_it_101 1) 4)
    (<= kidia (+ kfdia (- 1)))
    (<= (+ _for_it_99 2) 4)
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_99 1) _for_it_101)
  )
))

(check-sat)