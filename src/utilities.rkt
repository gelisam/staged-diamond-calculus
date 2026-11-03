#lang racket
(require (for-syntax racket/syntax))
(require rackunit)
(require data/union-find)

(provide
  and-let*
  my-struct my-struct*
  define-lambda-syntax define-application-syntax)

; (and-let* ([x e1] [y e2])
;   (+ x y))
; =>
; (let* ([x e1] [y e2])
;   (and x y (+ x y)))
(define-syntax (and-let* stx)
  (syntax-case stx ()
    [(_ () body ...)
     #`(begin body ...)]
    [(_ ([x1 e1] [x2 v2] ...) body ...)
     #`(let ([x1 e1])
         (and x1
              (and-let* ([x2 v2] ...) body ...)))]))
(check-equal? (and-let* ([x 1] [y 2])
                (+ x y))
              3)
(check-equal? (and-let* ([x 1] [y #f])
                (+ x y))
              #f)

; (get-symbols '([x e] e))
; =>
; '(x e e)
(define-for-syntax (get-symbols datum)
  (cond [(symbol? datum)
        (list datum)]
        [(null? datum)
        '()]
        [(pair? datum)
        (append (get-symbols (car datum))
                (get-symbols (cdr datum)))]
        [else
          (error 'get-symbols "unhandled datum [~v]" datum)]))

; (append-suffix-to-def #'(hello x y z) #'A)
; =>
; (helloA x y z)
(define-for-syntax (append-suffix-to-def def suffix)
  (syntax-case def ()
    [(name arg ...)
     (with-syntax ([name-with-suffix
                    (format-id #'name "~a~a" #'name suffix)])
       #'(name-with-suffix arg ...))]))

; (append-suffixes-to-defs
;   (list #'A #'B)
;   (list #'(hello) #'(world x)))
; =>
; (list (helloA)
;       (helloB)
;       (worldA x)
;       (worldB x))
(define-for-syntax (append-suffixes-to-defs suffixes defs)
  (for*/list ([def defs]
              [suffix suffixes])
    (append-suffix-to-def def suffix)))

; (my-struct (my-let [x e] e))
; =>
; (struct my-let (x1 e2 e3) #:transparent)
(define-syntax (my-struct stx)
  (syntax-case stx ()
    [(_ (name arg ...))
     (let* ([arg-list (get-symbols (syntax->datum #'(arg ...)))]
            [iarg-list (for/list ([(arg i) (in-indexed arg-list)])
                         (format-id #'name "~a~a" arg (+ i 1)))])
       #`(struct name #,iarg-list #:transparent))]))

; (my-struct*
;   (foo e e)
;   (bar)
;   (baz e)
;   (with-suffixes (A B "")
;     (hello)
;     (world)))
; =>
; (struct-n foo 2)
; (struct-n bar 0)
; (struct-n baz 1)
; (struct-n helloA 0)
; (struct-n worldA 0)
; (struct-n helloB 0)
; (struct-n worldB 0)
; (struct-n hello 0)
; (struct-n world 0)
(define-syntax (my-struct* stx)
  (syntax-case stx (with-suffixes)
    [(_)
     #'(begin)]
    [(_ (with-suffixes (suffix ...)
          def-needing-suffixes
          ...)
        def
        ...)
     (with-syntax ([(def-with-suffix ...)
                    (append-suffixes-to-defs
                      (syntax->list #'(suffix ...))
                      (syntax->list #'(def-needing-suffixes ...)))])
       #'(my-struct*
           def-with-suffix
           ...
           def
           ...))]
    [(_ first-def
        def
        ...)
     #'(begin
         (my-struct first-def)
         (my-struct*
           def
           ...))]))

; (define-lambda-syntax lam mk-lam mk-var)
; (lam (x y)
;   (app x y))
; =>
; (mk-lam 'x
;   (mk-lam 'y
;     (app (mk-var 'x) (mk-var 'y))))
(define-syntax-rule (define-lambda-syntax lam mk-lam mk-var)
  (begin
    ; (lam-mono x
    ;   (app x x))
    ; =>
    ; (mk-lam 'x
    ;   (app (mk-var 'x) (mk-var 'x)))
    (define-syntax-rule (lam-mono x body)
      (mk-lam 'x
        (let ([x (mk-var 'x)])
          body)))
    ; (lam (x y) body)
    ; =>
    ; (mk-lam 'x
    ;   (mk-lam 'y
    ;     body))
    (define-syntax (lam stx)
      (syntax-case stx ()
        [(_ () body)
         #'body]
        [(_ (x xs (... ...)) body)
         #'(lam-mono x (lam (xs (... ...)) body))]))))

; (define-application-syntax app mk-app)
; (app f x y z)
; =>
; (mk-app
;   (mk-app
;     (mk-app
;       (mk-var 'f)
;       (mk-var 'x))
;     (mk-var 'y))
;   (mk-var 'z))
(define-syntax-rule (define-application-syntax app mk-app)
  (define-syntax (app stx)
    (syntax-case stx ()
      [(_ fun arg)
      #'(mk-app
          fun
          arg)]
      [(_ fun arg (... ...) last-arg)
      #'(mk-app
          (app fun arg (... ...))
          last-arg)])))