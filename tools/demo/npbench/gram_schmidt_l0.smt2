

(assert (forall ((M Int) (N Int) (k Int))
  (=>
    (and
      (<= 1 (- M 1))
      (<= (+ k 2) (- N 1))
      (<= 1 (- N 1))
      (<= 0 k)
      (<= (+ k 1) (- N 1))
      (not (or (exists ((m_1 Int)) (and (<= 0 m_1) (<= m_1 (- M 1)) (= k (+ k 1)))) (exists ((j_0 Int)(j_1 Int)) (and (<= (+ k 2) j_1) (= j_0 j_1) (<= j_1 (- N 1)) (<= (+ k 1) j_0) (= k (+ k 1)) (<= j_0 (- N 1)))) (exists ((j_0 Int)(j_1 Int)(m_1 Int)) (and (<= (+ k 2) j_1) (<= m_1 (- M 1)) (<= 0 m_1) (<= j_1 (- N 1)) (or (and (= k (+ k 1)) (= j_0 j_1)) (and (<= 0 m_1) (<= m_1 (- M 1)) (= j_0 j_1))) (<= (+ k 1) j_0) (<= j_0 (- N 1)))) (exists ((j_1 Int)) (and (<= (+ k 2) j_1) (= k (+ k 1)) (<= j_1 (- N 1)) (= k j_1))) (exists ((j_1 Int)(m_0 Int)) (and (<= (+ k 2) j_1) (or (and (= k (+ k 1)) (= k j_1)) (and (<= m_0 (- M 1)) (= k (+ k 1)) (<= 0 m_0))) (<= j_1 (- N 1)) (<= 0 m_0) (<= m_0 (- M 1)))) (exists ((j_1 Int)(m_0 Int)(m_1 Int)) (and (<= 0 m_1) (<= m_1 (- M 1)) (<= (+ k 2) j_1) (<= j_1 (- N 1)) (or (and (= m_0 m_1) (= k j_1)) (and (= m_0 m_1) (= k (+ k 1)))) (<= 0 m_0) (<= m_0 (- M 1)))) (exists ((j_0 Int)(j_1 Int)(m_0 Int)) (and (<= (+ k 2) j_1) (or (and (<= m_0 (- M 1)) (= j_0 j_1) (<= 0 m_0)) (and (= k (+ k 1)) (= j_0 j_1))) (<= j_1 (- N 1)) (<= 0 m_0) (<= m_0 (- M 1)) (<= (+ k 1) j_0) (<= j_0 (- N 1)))) (exists ((j_1 Int)(m_1 Int)) (and (<= (+ k 2) j_1) (<= m_1 (- M 1)) (<= 0 m_1) (<= j_1 (- N 1)) (or (and (= k (+ k 1)) (= k j_1)) (and (<= 0 m_1) (<= m_1 (- M 1)) (= k j_1))))) (exists ((j_1 Int)(m_1 Int)) (and (<= (+ k 2) j_1) (<= m_1 (- M 1)) (<= 0 m_1) (<= j_1 (- N 1)) (= k j_1) (= k (+ k 1)))) (exists ((j_0 Int)(m_0 Int)) (and (<= 0 m_0) (<= m_0 (- M 1)) (<= (+ k 1) j_0) (or (and (= k (+ k 1)) (= j_0 (+ k 1))) (and (<= m_0 (- M 1)) (<= 0 m_0) (= j_0 (+ k 1)))) (<= j_0 (- N 1)))) (exists ((j_0 Int)) (and (<= (+ k 1) j_0) (= k (+ k 1)) (<= j_0 (- N 1)) (= j_0 (+ k 1)))) (exists ((j_0 Int)(m_0 Int)) (and (<= 0 m_0) (<= m_0 (- M 1)) (<= (+ k 1) j_0) (= k (+ k 1)) (<= j_0 (- N 1)) (= j_0 (+ k 1)))) (exists ((j_0 Int)(j_1 Int)(m_0 Int)(m_1 Int)) (and (<= (+ k 2) j_1) (<= m_1 (- M 1)) (<= 0 m_1) (= j_0 j_1) (<= j_1 (- N 1)) (<= 0 m_0) (<= m_0 (- M 1)) (<= (+ k 1) j_0) (= m_0 m_1) (<= j_0 (- N 1)))) (= k (+ k 1)) (exists ((m_0 Int)) (and (<= m_0 (- M 1)) (= k (+ k 1)) (<= 0 m_0))) (exists ((j_0 Int)(m_1 Int)) (and (<= 0 m_1) (<= m_1 (- M 1)) (<= (+ k 1) j_0) (or (and (= k (+ k 1)) (= j_0 (+ k 1))) (and (<= 0 m_1) (<= m_1 (- M 1)) (= k (+ k 1)))) (<= j_0 (- N 1)))) (exists ((m_0 Int)(m_1 Int)) (and (<= 0 m_1) (<= m_1 (- M 1)) (<= 0 m_0) (<= m_0 (- M 1)) (= m_0 m_1) (= k (+ k 1)))) (exists ((j_0 Int)(m_0 Int)(m_1 Int)) (and (<= 0 m_1) (<= m_1 (- M 1)) (<= 0 m_0) (<= m_0 (- M 1)) (<= (+ k 1) j_0) (or (and (= m_0 m_1) (= k (+ k 1))) (and (= m_0 m_1) (= j_0 (+ k 1)))) (<= j_0 (- N 1))))))
    )
    false
  )
))

(check-sat)