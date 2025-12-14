

(assert (forall ((M Int) (i Int) (k Int) (start_val (Array Int Int)) (stop_val (Array Int Int)))
  (=>
    false
    false
  )
))

(check-sat)