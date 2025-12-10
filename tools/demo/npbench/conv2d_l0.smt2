

(assert (forall ((C_in Int) (C_out Int) (H_out Int) (K Int) (N Int) (W_out Int) (i Int))
  (=>
    (and
      (not (or (exists ((j_1 Int)(n_batch_1 Int)(c_out_1 Int)(j_0 Int)(n_batch_0 Int)(c_out_0 Int)) (and (<= 0 j_1) (<= j_1 (- W_out 1)) (<= 0 n_batch_1) (<= n_batch_1 (- N 1)) (<= 0 c_out_1) (<= c_out_1 (- C_out 1)) (= n_batch_0 n_batch_1) (= i (+ i 1)) (= j_0 j_1) (= c_out_0 c_out_1) (<= 0 j_0) (<= j_0 (- W_out 1)) (<= 0 n_batch_0) (<= n_batch_0 (- N 1)) (<= 0 c_out_0) (<= c_out_0 (- C_out 1)))) (exists ((j_1 Int)(n_batch_1 Int)(c_out_1 Int)(k_row_1 Int)(j_0 Int)(k_col_1 Int)(c_in_loop_1 Int)(n_batch_0 Int)(c_out_0 Int)) (and (<= 0 j_1) (<= j_1 (- W_out 1)) (<= 0 n_batch_1) (<= n_batch_1 (- N 1)) (<= 0 c_out_1) (<= c_out_1 (- C_out 1)) (<= 0 k_row_1) (<= k_row_1 (- K 1)) (<= 0 k_col_1) (<= 0 j_0) (<= j_0 (- W_out 1)) (<= k_col_1 (- K 1)) (<= 0 c_in_loop_1) (<= c_in_loop_1 (- C_in 1)) (<= n_batch_0 (- N 1)) (<= 0 c_out_0) (<= c_out_0 (- C_out 1)) (<= 0 n_batch_0))) (exists ((j_1 Int)(n_batch_1 Int)(c_out_1 Int)(j_0 Int)(n_batch_0 Int)(c_out_0 Int)) (and (<= 0 j_1) (<= j_1 (- W_out 1)) (<= 0 n_batch_1) (<= n_batch_1 (- N 1)) (<= 0 c_out_1) (<= c_out_1 (- C_out 1)) (<= 0 j_0) (<= j_0 (- W_out 1)) (<= 0 n_batch_0) (<= n_batch_0 (- N 1)) (<= 0 c_out_0) (<= c_out_0 (- C_out 1)))) (exists ((j_1 Int)(k_col_0 Int)(n_batch_1 Int)(c_in_loop_0 Int)(c_out_1 Int)(j_0 Int)(n_batch_0 Int)(c_out_0 Int)(k_row_0 Int)) (and (<= k_row_0 (- K 1)) (<= 0 j_1) (<= j_1 (- W_out 1)) (<= 0 k_col_0) (<= k_col_0 (- K 1)) (<= 0 n_batch_1) (<= n_batch_1 (- N 1)) (<= 0 c_in_loop_0) (<= c_in_loop_0 (- C_in 1)) (<= 0 c_out_1) (<= c_out_1 (- C_out 1)) (<= 0 j_0) (<= j_0 (- W_out 1)) (<= 0 n_batch_0) (<= n_batch_0 (- N 1)) (<= 0 c_out_0) (<= c_out_0 (- C_out 1)) (<= 0 k_row_0))) (exists ((j_1 Int)(k_col_0 Int)(n_batch_1 Int)(c_in_loop_0 Int)(c_out_1 Int)(k_row_1 Int)(j_0 Int)(k_col_1 Int)(c_in_loop_1 Int)(n_batch_0 Int)(c_out_0 Int)(k_row_0 Int)) (and (<= 0 j_0) (<= j_0 (- W_out 1)) (<= 0 n_batch_0) (<= n_batch_0 (- N 1)) (<= 0 c_out_0) (<= c_out_0 (- C_out 1)) (<= 0 j_1) (<= j_1 (- W_out 1)) (<= 0 n_batch_1) (<= n_batch_1 (- N 1)) (<= 0 c_out_1) (<= c_out_1 (- C_out 1)) (<= 0 k_row_1) (<= k_row_1 (- K 1)) (<= 0 k_col_1) (<= k_col_1 (- K 1)) (<= 0 c_in_loop_1) (<= c_in_loop_1 (- C_in 1)) (<= 0 k_row_0) (<= k_row_0 (- K 1)) (<= 0 k_col_0) (<= k_col_0 (- K 1)) (<= 0 c_in_loop_0) (<= c_in_loop_0 (- C_in 1))))))
      (<= 1 (- C_in 1))
      (<= 1 (- K 1))
      (<= 1 (- C_out 1))
      (<= 1 (- N 1))
      (<= 1 (- W_out 1))
      (<= 1 (- H_out 1))
      (<= 0 i)
      (<= (+ i 1) (- H_out 1))
    )
    false
  )
))

(check-sat)