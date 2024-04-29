;;; Lambda-calculus impelmentation
;;;
;;; Richard Bachmann
;;; 2024-04-25
;;; 2024-04-27
;;; 2024-04-29
;;;
;;; Based on the definition of the lambda-calculus in chapter 1 of
;;; "Lambda-calculus and combinators: an introduction" by Hindley and Seldin.


;;; Representation of lambda terms

(define (make-atom symbol) (list '<atom> symbol))
(define (atom? x) (equal? (car x) '<atom>))
(define (atom-symbol x) (cadr x))

(define (make-application function argument) (list '<application> function argument))
(define (application? x) (equal? (car x) '<application>))
(define (application-function x) (cadr x))
(define (application-argument x) (caddr x))

(define (make-abstraction binding-variable body) (list '<abstraction> binding-variable body))
(define (abstraction? x) (equal? (car x) '<abstraction>))
(define (abstraction-binding-variable x) (cadr x))
(define (abstraction-body x) (caddr x))

(define (make-nested-abstractions binding-variables body)
  (if (null? binding-variables)
      body
      (make-abstraction (car binding-variables)
                        (make-nested-abstractions (cdr binding-variables) body))))

(define (make-nested-applications function arguments)
  (if (null? arguments) ; if not actually an application, just a term
      function
      (make-nested-applications (make-application function
                                                  (car arguments))
                                (cdr arguments))))

(define (term? x)
  (or (atom? x) (application? x) (abstraction? x)))

(define (identical? x y)
  (equal? x y))


;;; Parsing s-expressions into lambda terms

(define (parse-atom x)
  (if (and (symbol? x)
           (not (equal? x 'lambda)))
      (make-atom x)
      #f))

(define (parse-application x)
  (if (and (list? x)
           (>= (length x) 2))
      (let ((func (parse-term (car x)))
            (args (parse-arguments (cdr x))))
        (if (and func args)
            (make-nested-applications func args)
            #f))
      #f))

(define (parse-arguments x)
  (if (null? x)
      '()
      (let ((arg (parse-term (car x))))
        (if arg
            (cons arg (parse-arguments (cdr x)))
            #f))))

(define (parse-binding-variables x)
  (if (null? x)
      '()
      (let ((var (parse-atom (car x))))
        (if var ; if parsed successfully
            (cons var (parse-binding-variables (cdr x)))
            #f))))

(define (parse-abstraction x)
  (if (and (list? x)
           (equal? (length x) 3)
           (equal? (car x) 'lambda)
           (list? (cadr x)))
      (let ((vars (parse-binding-variables (cadr x)))
            (body (parse-term (caddr x))))
        (if (and vars body) ; if parses were successful
            (make-nested-abstractions vars body)
            #f))
      #f))
          

(define (parse-term x)
  ;; "or" returns the first non-false value
  (or (parse-atom x)
      (parse-application x)
      (parse-abstraction x)))


;;; Unparsing lambda terms into s-expressions

(define (unparse-term x)
  (cond ((atom? x) (atom-symbol x))
        ((application? x)
         (list (unparse-term (application-function x))
               (unparse-term (application-argument x))))
        ((abstraction? x)
         (list 'lambda
               (list (unparse-term (abstraction-binding-variable x)))
               (unparse-term (abstraction-body x))))))




(define (num-atoms x)
  (cond ((atom? x) 1)
        ((application? x)
         (+ (num-atoms (application-function x))
            (num-atoms (application-argument x))))
        ((abstraction? x)
         (+ 1 (num-atoms (abstraction-body x))))))

(define (occurs-in? x y)
  (or (identical? x y)
      (and (application? y)
           (or (occurs-in? x (application-function y))
               (occurs-in? x (application-argument y))))
      (and (lambda:abstraction? y)
           (or (identical? x (abstraction-binding-variable y))
               (occurs-in? x (abstraction-body y))))))

(define (bound-in? x y)
  (or (and (application? y)
           (or (bound-in? x (application-function y))
               (bound-in? x (application-argument y))))
      (and (lambda:abstraction? y)
           (or (identical? x (abstraction-binding-variable y))
               (bound-in? x (abstraction-body y))))))

(define (free-in? x m)
  (or (and (atom? m)
           (identical? x m))
      (and (application? m)
           (or (free-in? x (application-function m))
               (free-in? x (application-argument m))))
      (and (abstraction? m)
           (not (identical? x (abstraction-binding-variable m)))
           (free-in? x (abstraction-body m)))))

(define (free-variables m)
  (define (free m already-bound)
    (cond ((atom? m)
           (if (member m already-bound) '() (list m)))
          ((application? m)
           (append (free (application-function m) already-bound)
                   (free (application-argument m) already-bound)))
          ((abstraction? m)
           (free (abstraction-body m)
                 (cons (abstraction-binding-variable m) already-bound)))))
  (free m '()))

(define (closed-term? m)
  (null? (free-variables m)))

;; I tried to follow the book's definition as closely as possible.
(define (substitute n x m)
  (cond ((atom? m)
         (if (identical? x m) n m))
        ((application? m)
         (make-application (substitute n x (application-function m))
                           (substitute n x (application-argument m))))
        ((abstraction? m)
         (let* ((m-bv (abstraction-binding-variable m))
                (m-body (abstraction-body m))
                (fv-m-body (free-variables m-body))
                (fv-n (free-variables n)))
           (cond ((identical? x m-bv) m)
                 ((not (member x fv-m-body)) m)
                 ((not (member m-bv fv-n))
                  (make-abstraction m-bv (substitute n x m-body)))
                 (else
                  (let ((fresh (make-fresh-atom m-bv (append fv-m-body fv-n))))
                    (make-abstraction
                     fresh
                     (substitute n x (substitute fresh m-bv m-body))))))))))

;; Returns a symbol whose string is the same as the string of the "desired" symbol,
;; but with enough asterisks ("*") appended to it so that it doesn't appear in the "taken" list.
;; If desired doesn't appear in taken, then this procedure will simply return desired.
(define (make-fresh-atom desired taken)
  (if (member desired taken)
      (make-fresh-atom (string->symbol (string-append (symbol->string desired) "*"))
                       taken)
      desired))

(define (beta-redex? m)
  (and (application? m)
       (abstraction? (application-function m))
       (term? (application-argument m))))

(define (beta-contract m)
  (if (beta-redex? m)
      (substitute (application-argument m)
                  (abstraction-binding-variable (application-function m))
                  (abstraction-body (application-function m)))
      m))

(define (beta-normal-form? m)
  (or (atom? m)
      (and (application? m)
           (not (beta-redex? m))
           (beta-normal-form? (application-function m))
           (beta-normal-form? (application-argument m)))
      (and (abstraction? m)
           (beta-normal-form? (abstraction-body m)))))

(define (reduce-to-bnf m)
  (cond ((beta-normal-form? m) m)
        ((beta-redex? m)
         (reduce-to-bnf (beta-contract m)))
        ((application? m)
         (reduce-to-bnf
          (make-application (reduce-to-bnf (application-function m))
                            (reduce-to-bnf (application-argument m)))))
        ((abstraction? m)
         (make-abstraction (abstraction-binding-variable m)
                           (reduce-to-bnf (abstraction-body m))))))

(define ex-1.28-f
  '((lambda (x y z) (x z (y z)))
    ((lambda (x y) (y x)) u)
    ((lambda (x y) (y x)) v)
    w))


  
