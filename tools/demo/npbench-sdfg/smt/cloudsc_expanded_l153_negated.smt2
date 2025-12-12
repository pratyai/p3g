(declare-fun _for_it_103 () Int)
(declare-fun _for_it_104 () Int)
(declare-fun kfdia () Int)
(declare-fun kidia () Int)
(declare-fun klev () Int)
(declare-fun ncldtop () Int)

(assert (and
  (forall ((tmp_parfor_53_0 Int) (tmp_parfor_53_1 Int))
    (or
      (and
        (not (= tmp_parfor_53_0 tmp_parfor_53_1))
        (or
          (not (= tmp_parfor_53_0 tmp_parfor_53_1))
          (not (= _for_it_104 _for_it_103))
        )
        (or
          (not (= _for_it_103 (+ _for_it_104 1)))
          (not (= tmp_parfor_53_0 tmp_parfor_53_1))
        )
      )
      (not (<= tmp_parfor_53_1 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_53_1))
      (not (<= tmp_parfor_53_0 (+ kfdia (- 1))))
      (not (<= (+ kidia (- 1)) tmp_parfor_53_0))
    )
  )
  (and
    (<= ncldtop (+ klev (- 1)))
    (<= (+ _for_it_104 1) (+ _for_it_103 (- 1)))
    (<= 0 _for_it_104)
    (<= kidia (+ kfdia (- 1)))
    (<= 1 (+ _for_it_103 (- 1)))
  )
))

(check-sat)