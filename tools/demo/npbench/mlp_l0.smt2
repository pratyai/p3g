

(assert (forall ((C_in Int) (N Int) (S0 Int) (S1 Int) (S2 Int) (n_mlp Int))
  (=>
    (and
      (<= 0 n_mlp)
      (<= (+ n_mlp 1) (- N 1))
      (not (or (exists ((s0_mlp_1 Int)(k_matmul_1 Int)(s0_mlp_0 Int)(k_matmul_0 Int)) (and (<= 0 s0_mlp_0) (<= s0_mlp_0 (- S0 1)) (<= 0 s0_mlp_1) (<= s0_mlp_1 (- S0 1)) (= n_mlp (+ n_mlp 1)) (= s0_mlp_0 s0_mlp_1) (<= 0 k_matmul_1) (<= k_matmul_1 (- C_in 1)) (<= 0 k_matmul_0) (<= k_matmul_0 (- C_in 1)))) (exists ((s0_mlp_1 Int)(s0_mlp_0 Int)(k_matmul_0 Int)) (and (<= 0 s0_mlp_0) (<= s0_mlp_0 (- S0 1)) (<= 0 s0_mlp_1) (<= s0_mlp_1 (- S0 1)) (= n_mlp (+ n_mlp 1)) (= s0_mlp_0 s0_mlp_1) (<= 0 k_matmul_0) (<= k_matmul_0 (- C_in 1)))) (exists ((s0_mlp_1 Int)(k_matmul_1 Int)(s0_mlp_0 Int)) (and (<= 0 s0_mlp_0) (<= s0_mlp_0 (- S0 1)) (<= 0 s0_mlp_1) (<= s0_mlp_1 (- S0 1)) (= n_mlp (+ n_mlp 1)) (= s0_mlp_0 s0_mlp_1) (<= 0 k_matmul_1) (<= k_matmul_1 (- C_in 1)))) (exists ((s0_mlp_1 Int)(s0_mlp_0 Int)) (and (<= 0 s0_mlp_0) (<= s0_mlp_0 (- S0 1)) (<= 0 s0_mlp_1) (<= s0_mlp_1 (- S0 1)) (= n_mlp (+ n_mlp 1)) (= s0_mlp_0 s0_mlp_1)))))
      (<= 1 (- C_in 1))
      (<= 1 (- S0 1))
      (<= 1 (- N 1))
    )
    false
  )
))

(check-sat)