(declare-fun |id#1@1| () (_ BitVec 32))
(define-fun .10 () (_ BitVec 32) (_ bv10 32))
(define-fun .11 () (_ BitVec 32) |id#1@1|)
(define-fun .12 () Bool (bvslt .10 .11))
(assert .12)
(check-sat)
