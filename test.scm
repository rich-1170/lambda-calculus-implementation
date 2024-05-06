(import (lambda-calculus))

(define ex-1.14-a
  (lambda ()
    (unparse (substitute (parse '(u v))
                         (parse 'x)
                         (parse '(lambda (y) (x (lambda (w) (v w x)))))))))
