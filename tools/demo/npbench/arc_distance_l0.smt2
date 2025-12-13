

(assert (forall ((N Int) (idx Int))
  (=>
    (and
      (<= 0 idx)
      (<= (+ idx 1) (- N 1))
      (<= 1 (- N 1))
      (not (= idx (+ idx 1)))
    )
    false
  )
))

(check-sat)