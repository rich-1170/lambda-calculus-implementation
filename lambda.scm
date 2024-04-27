;;; Lambda-calculus impelmentation
;;;
;;; Richard Bachmann
;;; 2024-04-25
;;; 2024-04-27
;;;
;;; Based on the definition of the lambda-calculus in chapter 1 of
;;; "Lambda-calculus and combinators: an introduction" by Hindley and Seldin.

(define (lambda:atom? x)
  ;; 'lambda is a reserved word in this implementation.
  (and (symbol? x)
       (not (equal? x 'lambda))))

(define (lambda:abstraction? x)
  ;; Does x have the form '(lambda (<atom>) <term>) ?
  ;; Note: abstractions involving more than one binding variable are not allowed.
  (and (list? x)
       (equal? (length x) 3)
       (equal? (car x) 'lambda)
       (list? (cadr x))
       (equal? (length (cadr x)) 1)
       (lambda:atom? (caadr x))
       (lambda:term? (caddr x))))

(define (lambda:abstraction-binding-variable x) (caadr x))
(define (lambda:abstraction-body x) (caddr x))
(define lambda:abstraction-scope lambda:abstraction-body)
(define (lambda:make-abstraction var body)
  (list 'lambda (list var) body))

(define (lambda:application? x)
  ;; Does x have the form '(<term> <term>) ?
  (and (list? x)
       (equal? (length x) 2)
       (lambda:term? (car x))
       (lambda:term? (cadr x))))

(define (lambda:application-function x) (car x))
(define (lambda:application-argument x) (cadr x))

(define (lambda:make-application p q) (list p q))

(define (lambda:term? x)
  (or (lambda:atom? x)
      (lambda:abstraction? x)
      (lambda:application? x)))

(define (lambda:same? x y)
  (equal? x y))
(define lambda:syntactically-identical? lambda:same?)

(define (lambda:length x)
  (cond ((lambda:atom? x) 1)
        ((lambda:application? x)
         (+ (lambda:length (lambda:application-function x))
            (lambda:length (lambda:application-argument x))))
        ((lambda:abstraction? x)
         (+ 1 (lambda:length (lambda:abstraction-body x))))))

(define (lambda:occurs-in? x m)
  (or (lambda:same? x m)
      (and (lambda:application? m)
           (lambda:occurs-in? x (lambda:application-function m))
           (lambda:occurs-in? x (lambda:application-argument m)))
      (and (lambda:abstraction? m)
           (lambda:same? x (lambda:abstraction-binding-variable m))
           (lambda:occurs-in x (lambda:abstraction-body m)))))

(define (lambda:bound-in? x m)
  (or (and (lambda:application? m)
           (or (lambda:bound-in? x (lambda:application-function m))
               (lambda:bound-in? x (lambda:application-argument m)))
      (and (lambda:abstraction? m)
           (lambda:same? x (lambda:abstraction-binding-variable m))
           (lambda:occurs-in? x (lambda:abstraction-body m)))
      (and (lambda:abstraction? m)
           (lambda:bound-in? x (lambda:abstraction-body m))))))

(define (lambda:binding-in? x m)
  (or (and (lambda:application? m)
           (or (lambda:binding-in? x (lambda:application-function m))
               (lambda:binding-in? x (lambda:application-argument m))))
      (and (lambda:abstraction? m)
           (or (lambda:same? x (lambda:abstraction-binding-variable m))
               (lambda:binding-in? x (lambda:abstraction-body m))))))

(define (lambda:free-in? x m)
  (or (and (lambda:atom? m)
           (lambda:same? x m))
      (and (lambda:application? m)
           (or (lambda:free-in? x (lambda:application-function m))
               (lambda:free-in? x (lambda:application-argument m))))
      (and (lambda:abstraction? m)
           (not (lambda:same? x (lambda:abstraction-binding-variable m)))
           (lambda:free-in? x (lambda:abstraction-body m)))))

;; bound-variables is a list of variables that are bound in abstractions surrounding m.
;; Provide an empty list if there is nothing surrounding m.
(define (lambda:free-variables m bound-variables)
  (cond ((lambda:atom? m)
         (if (member m bound-variables) '() (list m)))
        ((lambda:application? m)
         (append (lambda:free-variables (lambda:application-function m) bound-variables)
                 (lambda:free-variables (lambda:application-argument m) bound-variables)))
        ((lambda:abstraction? m)
         (lambda:free-variables (lambda:abstraction-body m)
                                (cons (lambda:abstraction-binding-variable m) bound-variables)))))

(define (lambda:closed-term? m)
  (null? (lambda:free-variables m '())))

;; I tried to follow the book's definition as closely as possible.
(define (lambda:substitute n x m)
  (cond ((lambda:atom? m)
         (if (lambda:same? x m) n m))
        ((lambda:application? m)
         (lambda:make-application (lambda:substitute n x (lambda:application-function m))
                                  (lambda:substitute n x (lambda:application-argument m))))
        ((lambda:abstraction? m)
         (let* ((m-bv (lambda:abstraction-binding-variable m))
                (m-body (lambda:abstraction-body m))
                (fv-m-body (lambda:free-variables m-body '()))
                (fv-n (lambda:free-variables n '())))
           (cond ((lambda:same? x m-bv) m)
                 ((not (member x fv-m-body)) m)
                 ((not (member m-bv fv-n))
                  (lambda:make-abstraction m-bv (lambda:substitute n x m-body)))
                 (else
                  (let ((fresh (lambda:make-fresh-symbol m-bv (append fv-m-body fv-n))))
                    (lambda:make-abstraction
                     fresh
                     (lambda:substitute n x (lambda:substitute fresh m-bv m-body))))))))))

;; Returns a symbol whose string is the same as the string of the "desired" symbol,
;; but with enough asterisks ("*") appended to it so that it doesn't appear in the "taken" list.
;; If desired doesn't appear in taken, then this procedure will simply return desired.
(define (lambda:make-fresh-symbol desired taken)
  (if (member desired taken)
      (lambda:make-fresh-symbol (string->symbol (string-append (symbol->string desired) "*"))
                                taken)
      desired))

(define (lambda:beta-redex? m)
  (and (lambda:application? m)
       (lambda:abstraction? (lambda:application-function m))
       (lambda:term? (lambda:application-argument m))))

(define (lambda:beta-contract m)
  (if (lambda:beta-redex? m)
      (lambda:substitute (lambda:application-argument m)
                         (lambda:abstraction-binding-variable (lambda:application-function m))
                         (lambda:abstraction-body (lambda:application-function m)))
      m))

(define (lambda:beta-normal-form? m)
  (or (lambda:atom? m)
      (and (lambda:application? m)
           (not (lambda:beta-redex? m))
           (lambda:beta-normal-form? (lambda:application-function m))
           (lambda:beta-normal-form? (lambda:application-argument m)))
      (and (lambda:abstraction? m)
           (lambda:beta-normal-form? (lambda:abstraction-body m)))))

(define (lambda:reduce-to-bnf m)
  (cond ((lambda:beta-normal-form? m) m)
        ((lambda:beta-redex? m)
         (lambda:reduce-to-bnf (lambda:beta-contract m)))
        ((lambda:application? m)
         (lambda:reduce-to-bnf
          (lambda:make-application (lambda:reduce-to-bnf (lambda:application-function m))
                                   (lambda:reduce-to-bnf (lambda:application-argument m)))))
        ((lambda:abstraction? m)
         (lambda:make-abstraction (lambda:abstraction-binding-variable m)
                                  (lambda:reduce-to-bnf (lambda:abstraction-body m))))))

(define ex-1.28-f
  '((((lambda (x)
        (lambda (y)
          (lambda (z)
            ((x z) (y z)))))
      ((lambda (x)
         (lambda (y)
           (y x)))
       u))
     ((lambda (x)
        (lambda (y)
          (y x)))
      v))
    w))


  
