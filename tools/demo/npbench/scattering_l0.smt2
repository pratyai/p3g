(declare-fun Norb () Int)

(assert (forall ((N3D Int) (NA Int) (NB Int) (NE Int) (Nkz Int) (Nqz Int) (Nw Int) (k Int))
  (=>
    (and
      (not (exists ((i_1 Int)(w_0 Int)(j_1 Int)(i_0 Int)(a_1 Int)(j_0 Int)(a_0 Int)(b_1 Int)(b_0 Int)(E_1 Int)(q_0 Int)(E_0 Int)(q_1 Int)(w_1 Int)) (and (= a_0 a_1) (<= 1 Norb) (<= w_1 E_1) (<= w_0 E_0) (<= 0 E_0) (<= E_0 (- NE 1)) (<= 0 q_0) (<= q_0 (- Nqz 1)) (<= 0 w_0) (<= w_0 (- Nw 1)) (<= 0 i_0) (<= i_0 (- N3D 1)) (<= 0 j_0) (<= j_0 (- N3D 1)) (<= 0 a_0) (<= a_0 (- NA 1)) (<= 0 b_0) (<= b_0 (- NB 1)) (<= 0 E_1) (<= E_1 (- NE 1)) (<= 0 q_1) (<= q_1 (- Nqz 1)) (<= 0 w_1) (<= w_1 (- Nw 1)) (<= 0 i_1) (<= i_1 (- N3D 1)) (<= 0 j_1) (<= j_1 (- N3D 1)) (<= 0 a_1) (<= a_1 (- NA 1)) (<= 0 b_1) (<= b_1 (- NB 1)) (= k (+ k 1)) (= E_0 E_1))))
      (<= 0 k)
      (<= (+ k 1) (- Nkz 1))
      (<= 1 (- NB 1))
      (<= 1 (- NA 1))
      (<= 1 (- N3D 1))
      (<= 1 (- Nw 1))
      (<= 1 (- Nqz 1))
      (<= 1 (- NE 1))
      (<= 1 (- Nkz 1))
    )
    false
  )
))

(check-sat)