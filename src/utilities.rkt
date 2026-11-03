#lang racket
(require (for-syntax racket/syntax))
(require rackunit)
(require data/union-find)

(provide
  and-let*
  my-struct my-struct*)


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

; (my-struct* (foo e e) (bar) (baz e))
; =>
; (struct-n foo 2)
; (struct-n bar 0)
; (struct-n baz 1)
(define-syntax (my-struct* stx)
  (syntax-case stx ()
    [(_ def ...)
     #'(begin
         (my-struct def) ...)]))
