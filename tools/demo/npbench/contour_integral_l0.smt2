

(assert (forall ((NM Int) (NR Int) (idx Int) (slab_per_bc Int))
  (=>
    (and
      (not (or (<= 1 NR) (exists ((c_0 Int)(c_1 Int)(r_0 Int)(r_1 Int)) (and (<= r_0 (- NR 1)) (<= 0 c_0) (= r_0 r_1) (= c_0 c_1) (<= 0 r_1) (<= r_1 (- NR 1)) (<= c_1 (- NM 1)) (<= 0 c_1) (<= c_0 (- NM 1)) (<= 0 r_0))) (exists ((c_1 Int)(n_1 Int)(r_1 Int)) (and (<= 0 n_1) (<= n_1 slab_per_bc) (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_1 (- NR 1)))) (and (<= 1 NR) (<= 1 NM)) (exists ((c_1 Int)(r_1 Int)) (and (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_1 (- NM 1)))) (exists ((n_0 Int)(c_0 Int)(r_0 Int)) (and (<= r_0 (- NR 1)) (<= 0 c_0) (<= c_0 (- NR 1)) (<= 0 n_0) (<= n_0 slab_per_bc) (<= 0 r_0))) (exists ((c_0 Int)(n_1 Int)(r_1 Int)(c_1 Int)(n_0 Int)(r_0 Int)) (and (<= r_0 (- NR 1)) (<= 0 c_0) (<= c_0 (- NR 1)) (= r_0 r_1) (= c_0 c_1) (<= 0 n_1) (<= n_1 slab_per_bc) (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_1 (- NR 1)) (<= 0 n_0) (<= n_0 slab_per_bc) (<= 0 r_0))) (exists ((c_0 Int)(r_0 Int)) (and (<= r_0 (- NR 1)) (<= 0 c_0) (<= c_0 (- NM 1)) (<= 0 r_0)))))
      (<= 0 idx)
      (<= (+ idx 1) 31)
      (<= 1 (- NM 1))
      (<= 1 (- NR 1))
      (<= 1 slab_per_bc)
    )
    false
  )
))

(check-sat)