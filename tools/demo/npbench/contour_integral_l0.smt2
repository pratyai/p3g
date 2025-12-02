

(assert (forall ((NM Int) (NR Int) (idx Int) (slab_per_bc Int))
  (=>
    (and
      (<= 1 (- NR 1))
      (<= (+ idx 1) 31)
      (<= 1 slab_per_bc)
      (not (or (<= 1 NR) (exists ((r_0 Int)(c_1 Int)(c_0 Int)(r_1 Int)) (and (<= 0 r_0) (<= r_0 (- NR 1)) (<= 0 c_0) (= r_0 r_1) (= c_0 c_1) (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_0 (- NM 1)) (<= c_1 (- NM 1)))) (exists ((r_0 Int)(n_0 Int)(c_0 Int)) (and (<= 0 r_0) (<= r_0 (- NR 1)) (<= 0 c_0) (<= c_0 (- NR 1)) (<= 0 n_0) (<= n_0 slab_per_bc))) (exists ((r_0 Int)(c_0 Int)(n_1 Int)(r_1 Int)(c_1 Int)(n_0 Int)) (and (<= 0 r_0) (<= r_0 (- NR 1)) (<= 0 c_0) (<= c_0 (- NR 1)) (= r_0 r_1) (= c_0 c_1) (<= 0 n_1) (<= n_1 slab_per_bc) (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_1 (- NR 1)) (<= 0 n_0) (<= n_0 slab_per_bc))) (exists ((c_1 Int)(n_1 Int)(r_1 Int)) (and (<= 0 n_1) (<= n_1 slab_per_bc) (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_1 (- NR 1)))) (exists ((r_0 Int)(c_0 Int)) (and (<= 0 r_0) (<= r_0 (- NR 1)) (<= 0 c_0) (<= c_0 (- NM 1)))) (and (<= 1 NR) (<= 1 NM)) (exists ((c_1 Int)(r_1 Int)) (and (<= 0 r_1) (<= r_1 (- NR 1)) (<= 0 c_1) (<= c_1 (- NM 1))))))
      (<= 0 idx)
      (<= 1 (- NM 1))
    )
    false
  )
))

(check-sat)