#lang racket
(require (for-syntax racket/syntax))
(require rackunit)
(require data/union-find)


;;;;;;;;;;;;;
; utilities ;
;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;
; raw syntax ;
;;;;;;;;;;;;;;

; phase 1 terms with phase 0 terms inside of them
; e1 ::= x1 | \x1. e1 | e1 e1
;      | zero | succ | case-nat e1 of {zero -> e1; succ x1 -> e1}
;      | 'e0 | let-dia1 x0 = e1 in e1
(my-struct*
  (mk-var1 x1)
  (mk-λ1 (x1) e1)
  (mk-app1 e1 e1)
  (mk-let-fun1 [(e1 t1? x1) e1] e1)
  (mk-zero1)
  (mk-succ1)
  (mk-case-nat1 e1 [#|zero|# e1] [(#|succ|# x1) e1])
  (mk-quote1 e0)
  (mk-let-dia1 [x0 t1? e1] e1))

; Unexpanded phase 0 terms with phase 1 terms inside of them
; e0 ::= x0 | \x0. e0 | e0 e0
;      | zero | succ | case-nat e0 of {zero -> e0; succ x0 -> e0}
;      | $e1 | let-macro0 x1 = e1 in e0
(my-struct*
  (mk-var0 x0)
  (mk-λ0 (x0) e0)
  (mk-app0 e0 e0)
  (mk-let-fun0 [(e0 t? x0) e0] e0)
  (mk-zero0)
  (mk-succ0)
  (mk-case-nat0 e0 [#|zero|# e0] [(#|succ|# x0) e0])
  (mk-splice0 e1)
  (mk-let-macro0 [x1 t1? e1] e0))

; Expanded phase 0 terms, with no phase 1 terms
; e ::= x | \x. e | e e
;      | zero | succ | case-nat e of {zero -> e; succ x -> e}
(my-struct*
  (mk-var x)
  (mk-λ (x) e)
  (mk-app e e)
  (mk-let-fun [(e t? x) e] e)
  (mk-zero)
  (mk-succ)
  (mk-case-nat e [#|zero|# e] [(#|succ|# x) e]))

; phase 1 types with phase 0 types inside of them
; t1 ::= t1 -> t1 | Nat1 | Dia t
(my-struct*
  (Arrow1 t1 t1)
  (Nat1)
  (Dia1 t))

; phase 0 types with no phase 1 types
; t ::= t -> t | Nat
(my-struct*
  (Arrow t t)
  (Nat))


;;;;;;;;;;;;;;;;;;;
; syntactic sugar ;
;;;;;;;;;;;;;;;;;;;

; basic syntax sugar for phase 1 terms

(define-syntax-rule (λ1-mono x body)
  (mk-λ1 'x
    (let ([x (mk-var1 'x)])
      body)))
(check-equal? (λ1-mono x1 x1)
              (mk-λ1 'x1 (mk-var1 'x1)))

(define-syntax (λ1 stx)
  (syntax-case stx ()
    [(_ () body1)
     #'body1]
    [(_ (x xs ...) body1)
     #'(λ1-mono x (λ1 (xs ...) body1))]))
(check-equal? (λ1 (x1 y1) x1)
              (mk-λ1 'x1
                (mk-λ1 'y1
                  (mk-var1 'x1))))

(define-syntax (app1 stx)
  (syntax-case stx ()
    [(_ fun1 arg1)
     #'(mk-app1 fun1 arg1)]
    [(_ fun1 arg1s ... arg1)
     #'(mk-app1 (app1 fun1 arg1s ...) arg1)]))
(check-equal? (app1 (mk-var1 'f) (mk-var1 'x) (mk-var1 'y) (mk-var1 'z))
              (mk-app1
                (mk-app1
                  (mk-app1
                    (mk-var1 'f)
                    (mk-var1 'x))
                  (mk-var1 'y))
                (mk-var1 'z)))

(define-syntax (let-fun1 stx)
  (syntax-case stx ()
    [(_ [(fun x y ...) def] body)
     #'(mk-let-fun1 'fun #f 'x
         (let ([fun (mk-var1 'fun)]
               [x (mk-var1 'x)])
           (λ1 (y ...) def))
         (let ([fun (mk-var1 'fun)])
           body))]))
(check-equal? (let-fun1 [(f x) (app1 f x)]
                (app1 f (mk-zero1)))
              (mk-let-fun1 'f #f 'x
                (mk-app1 (mk-var1 'f) (mk-var1 'x))
                (mk-app1 (mk-var1 'f) (mk-zero1))))
(check-equal? (let-fun1 [(f x y) (app1 f x y)]
                (app1 f (mk-zero1) (mk-zero1)))
              (mk-let-fun1 'f #f 'x
                (mk-λ1 'y (app1 (mk-var1 'f) (mk-var1 'x) (mk-var1 'y)))
                (app1 (mk-var1 'f) (mk-zero1) (mk-zero1))))

(define zero1 (mk-zero1))
(define succ1 (mk-succ1))

(define (nat1 n)
  (if (zero? n)
      zero1
      (app1 succ1 (nat1 (- n 1)))))

(define-syntax case-nat1
  (syntax-rules (zero1 succ1)
    [(_ scrut1 [zero1 zero-branch1] [(succ1 x) succ-branch1])
     (mk-case-nat1 scrut1
       zero-branch1
       'x (let ([x (mk-var1 'x)])
            succ-branch1))]))
(check-equal? (case-nat1 zero1
                [zero1
                 zero1]
                [(succ1 x1)
                 (app1 succ1 x1)])
              (mk-case-nat1 (mk-zero1)
                (mk-zero1)
                'x1 (mk-app1 (mk-succ1) (mk-var1 'x1))))

; basic syntax sugar for unexpanded phase 0 terms

(define-syntax-rule (λ0-mono x body)
  (mk-λ0 'x
    (let ([x (mk-var0 'x)])
      body)))
(check-equal? (λ0-mono x0 x0)
              (mk-λ0 'x0 (mk-var0 'x0)))

(define-syntax (λ0 stx)
  (syntax-case stx ()
    [(_ () body0)
     #'body0]
    [(_ (x xs ...) body0)
     #'(λ0-mono x (λ0 (xs ...) body0))]))
(check-equal? (λ0 (x0 y0) x0)
              (mk-λ0 'x0
                (mk-λ0 'y0
                  (mk-var0 'x0))))

(define-syntax (app0 stx)
  (syntax-case stx ()
    [(_ fun0 arg0)
     #'(mk-app0 fun0 arg0)]
    [(_ fun0 arg0s ... arg0)
     #'(mk-app0 (app0 fun0 arg0s ...) arg0)]))
(check-equal? (app0 (mk-var0 'f) (mk-var0 'x) (mk-var0 'y) (mk-var0 'z))
              (mk-app0
                (mk-app0
                  (mk-app0
                    (mk-var0 'f)
                    (mk-var0 'x))
                  (mk-var0 'y))
                (mk-var0 'z)))

(define-syntax (let-fun0 stx)
  (syntax-case stx ()
    [(_ [(fun x y ...) def] body)
     #'(mk-let-fun0 'fun #f 'x
         (let ([fun (mk-var0 'fun)]
               [x (mk-var0 'x)])
           (λ0 (y ...) def))
         (let ([fun (mk-var0 'fun)])
           body))]))
(check-equal? (let-fun0 [(f x) (app0 f x)]
                (app0 f (mk-zero0)))
              (mk-let-fun0 'f #f 'x
                (mk-app0 (mk-var0 'f) (mk-var0 'x))
                (mk-app0 (mk-var0 'f) (mk-zero0))))
(check-equal? (let-fun0 [(f x y) (app0 f x y)]
                (app0 f (mk-zero0) (mk-zero0)))
              (mk-let-fun0 'f #f 'x
                (mk-λ0 'y (app0 (mk-var0 'f) (mk-var0 'x) (mk-var0 'y)))
                (app0 (mk-var0 'f) (mk-zero0) (mk-zero0))))

(define zero0 (mk-zero0))
(define succ0 (mk-succ0))

(define (nat0 n)
  (if (zero? n)
      zero0
      (app0 succ0 (nat0 (- n 1)))))

(define-syntax case-nat0
  (syntax-rules (zero0 succ0)
    [(_ scrut0 [zero0 zero-branch0] [(succ0 x) succ-branch0])
     (mk-case-nat0 scrut0
       zero-branch0
       'x (let ([x (mk-var0 'x)])
            succ-branch0))]))
(check-equal? (case-nat0 zero0
                [zero0
                 zero0]
                [(succ0 x0)
                 (app0 succ0 x0)])
              (mk-case-nat0 (mk-zero0)
                (mk-zero0)
                'x0 (mk-app0 (mk-succ0) (mk-var0 'x0))))

; basic syntax sugar for expanded terms

(define-syntax-rule (λ-mono x body)
  (mk-λ 'x
    (let ([x (mk-var 'x)])
      body)))
(check-equal? (λ-mono x x)
              (mk-λ 'x (mk-var 'x)))

(define-syntax (λ stx)
  (syntax-case stx ()
    [(_ () body)
     #'body]
    [(_ (x xs ...) body)
     #'(λ-mono x (λ (xs ...) body))]))
(check-equal? (λ (x y) x)
              (mk-λ 'x
                (mk-λ 'y
                  (mk-var 'x))))

(define-syntax (app stx)
  (syntax-case stx ()
    [(_ fun arg)
     #'(mk-app fun arg)]
    [(_ fun args ... arg)
     #'(mk-app (app fun args ...) arg)]))
(check-equal? (app (mk-var 'f) (mk-var 'x) (mk-var 'y) (mk-var 'z))
              (mk-app
                (mk-app
                  (mk-app
                    (mk-var 'f)
                    (mk-var 'x))
                  (mk-var 'y))
                (mk-var 'z)))

(define-syntax (let-fun stx)
  (syntax-case stx ()
    [(_ [(fun x y ...) def] body)
     #'(mk-let-fun 'fun #f 'x
         (let ([fun (mk-var 'fun)]
               [x (mk-var 'x)])
           (λ (y ...) def))
         (let ([fun (mk-var 'fun)])
           body))]))
(check-equal? (let-fun [(f x) (app f x)]
                (app f (mk-zero)))
              (mk-let-fun 'f #f 'x
                (mk-app (mk-var 'f) (mk-var 'x))
                (mk-app (mk-var 'f) (mk-zero))))
(check-equal? (let-fun [(f x y) (app f x y)]
                (app f (mk-zero) (mk-zero)))
              (mk-let-fun 'f #f 'x
                (mk-λ 'y (app (mk-var 'f) (mk-var 'x) (mk-var 'y)))
                (app (mk-var 'f) (mk-zero) (mk-zero))))

(define zero (mk-zero))
(define succ (mk-succ))

(define (nat n)
  (if (zero? n)
      zero
      (app succ (nat (- n 1)))))

(define-syntax case-nat
  (syntax-rules (zero succ)
    [(_ scrut [zero zero-branch] [(succ x) succ-branch])
     (mk-case-nat scrut
       zero-branch
       'x (let ([x (mk-var 'x)])
            succ-branch))]))
(check-equal? (case-nat zero
                [zero
                 zero]
                [(succ x)
                 (app succ x)])
              (mk-case-nat (mk-zero)
                (mk-zero)
                'x (mk-app (mk-succ) (mk-var 'x))))

; more interesting syntax sugar with let-dia1, quote1, let-macro0, and splice0

(define-syntax-rule (let-dia1 [x def1] body1)
  (mk-let-dia1 'x #f def1
    (let ([x (mk-var0 'x)])
      body1)))
(define (quote1 body0) (mk-quote1 body0))
(check-equal? (let-dia1 [one (nat0 1)]
                (quote1 (app0 one zero0)))
              (mk-let-dia1 'one #f (mk-app0 (mk-succ0) (mk-zero0))
                (mk-quote1 (mk-app0 (mk-var0 'one) (mk-zero0)))))

(define-syntax-rule (let-macro01 [x def1] body0)
  (mk-let-macro0 'x #f def1
    (let ([x (mk-var1 'x)])
      body0)))
(define-syntax (let-macro0 stx)
  (syntax-case stx ()
    [(_ [(f x ...) def1] body0)
     #'(let-macro01 [f (λ1 (x ...) def1)] body0)]
    [(_ [f def1] body0)
     #'(let-macro01 [f def1] body0)]))
(define (splice0 term1) (mk-splice0 term1))
(check-equal? (let-macro0 [one (nat1 1)]
                (splice0 (app1 (mk-var0 'f) one)))
              (mk-let-macro0 'one #f (mk-app1 (mk-succ1) (mk-zero1))
                (mk-splice0 (mk-app1 (mk-var0 'f) (mk-var1 'one)))))
(check-equal? (let-macro0 [(f x) (app1 succ1 x)]
                (splice0 (app1 f (quote1 (mk-var1 'one)))))
              (mk-let-macro0 'f #f (mk-λ1 'x (mk-app1 (mk-succ1) (mk-var1 'x)))
                (mk-splice0 (mk-app1 (mk-var1 'f) (mk-quote1 (mk-var1 'one))))))


;;;;;;;;;;;;;;;
; unification ;
;;;;;;;;;;;;;;;

(define (new-uf-set)
  (uf-new #f))

(define (occurs? uf-set t)
  (match t
    [(? uf-set? other-uf-set)
     (uf-same-set? uf-set other-uf-set)]
    [(Arrow1 ta tb)
     (or (occurs? uf-set ta)
         (occurs? uf-set tb))]
    [(Arrow ta tb)
     (or (occurs? uf-set ta)
         (occurs? uf-set tb))]
    [(Nat1) #f]
    [(Nat) #f]
    [(Dia1 t)
     (occurs? uf-set t)]))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)])
  (check-equal? (occurs? uf-set-a (Arrow1 (Nat1) (Nat1))) #f)
  (check-equal? (occurs? uf-set-a (Arrow1 (Nat1) uf-set-a)) #t)
  (check-equal? (occurs? uf-set-a (Arrow1 (Nat1) uf-set-b)) #f))

(define (zonk1 t)
  (if (uf-set? t)
      (or (uf-find t)
          t)
      t))
(define (zonk t)
  (match (zonk1 t)
    [(? uf-set? uf-set)
     uf-set]
    [(Arrow1 in-t out-t)
     (Arrow1 (zonk in-t)
             (zonk out-t))]
    [(Arrow in-t out-t)
     (Arrow (zonk in-t)
             (zonk out-t))]
    [(Nat1)
     (Nat1)]
    [(Nat)
     (Nat)]
    [(Dia1 lower-t)
     (Dia1 (zonk lower-t))]))

(define (equivalent? ta tb)
  (let ([zonked1-ta (zonk1 ta)]
        [zonked1-tb (zonk1 tb)])
    (match (list zonked1-ta zonked1-tb)
      [(list (? uf-set? uf-set-a)
             (? uf-set? uf-set-b))
       (uf-same-set? uf-set-a uf-set-b)]
      [(list (Arrow1 in-a out-a)
             (Arrow1 in-b out-b))
       (and (equivalent? in-a in-b)
            (equivalent? out-a out-b))]
      [(list (Arrow in-a out-a)
             (Arrow in-b out-b))
       (and (equivalent? in-a in-b)
            (equivalent? out-a out-b))]
      [(list (Nat1)
             (Nat1))
       #t]
      [(list (Nat)
             (Nat))
       #t]
      [(list (Dia1 lower-ta)
             (Dia1 lower-tb))
       (equivalent? lower-ta lower-tb)]
      [_
       #f])))

(define (unify ta tb)
  (let ([zonked1-ta (zonk1 ta)]
        [zonked1-tb (zonk1 tb)])
    (match (list zonked1-ta zonked1-tb)
      [(list (? uf-set? uf-set-a)
             (? uf-set? uf-set-b))
       (uf-union! uf-set-a uf-set-b)
       uf-set-a]
      [(or (list (? uf-set? uf-set)
                 t)
           (list t
                 (? uf-set? uf-set)))
       (if (occurs? uf-set t)
           (error "occurs-check")
           (begin
             (uf-set-canonical! uf-set t)
             t))]
      [(list (Arrow1 in-a out-a)
             (Arrow1 in-b out-b))
       (and-let* ([in (unify in-a in-b)]
                  [out (unify out-a out-b)])
         (Arrow1 in out))]
      [(list (Arrow in-a out-a)
             (Arrow in-b out-b))
       (and-let* ([in (unify in-a in-b)]
                  [out (unify out-a out-b)])
         (Arrow in out))]
      [(list (Nat1)
             (Nat1))
       (Nat1)]
      [(list (Nat)
             (Nat))
       (Nat)]
      [(list (Dia1 lower-ta)
             (Dia1 lower-tb))
       (and-let* ([lower (unify lower-ta lower-tb)])
         (Dia1 lower))]
      [_
       #f])))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)])
  (check-equal? (unify (Arrow1 (Nat1) (Nat1))
                       (Nat1))
                #f)
  (check-equal? (unify (Arrow1 (Nat1) (Nat1))
                       (Arrow1 (Nat1) (Nat1)))
                (Arrow1 (Nat1) (Nat1)))
  (check-equal? (unify (Arrow1 uf-set-a (Nat1))
                       (Arrow1 (Nat1) uf-set-b))
                (Arrow1 (Nat1) (Nat1)))
  (check-equal? (zonk1 uf-set-a) (Nat1))
  (check-equal? (zonk1 uf-set-b) (Nat1)))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)])
  (check-equal? (uf-same-set? uf-set-a uf-set-b)
                #f)
  (check-equal? (equivalent?
                  (unify (Arrow1 uf-set-a uf-set-b)
                         (Arrow1 uf-set-b uf-set-a))
                  (Arrow1 uf-set-a uf-set-a))
                #t))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)]
      [uf-set-c (new-uf-set)]
      [uf-set-d (new-uf-set)])
  (check-equal? (equivalent?
                  (unify (Arrow1 uf-set-a uf-set-b)
                         (Arrow1 uf-set-c uf-set-d))
                  (Arrow1 uf-set-a uf-set-a))
                #f))
(let ([uf-set-a (new-uf-set)])
  (check-exn #rx"occurs-check" (lambda ()
    (unify uf-set-a
           (Arrow1 uf-set-a uf-set-a)))))


;;;;;;;;;;;;;;;;
; type checker ;
;;;;;;;;;;;;;;;;

; typing rules for phase 1 terms
;
; x1 : t1 ∈ Γ1
; ------
; Γ1; Γ ⊢1 x1 : t1
;
; Γ1, x1 : in-t1; Γ ⊢1 body1 : out-t1
; ------
; Γ1; Γ ⊢1 \x1. body1 : in-t1 -> out-t1
;
; Γ1; Γ ⊢1 fun1 : in-t1 -> out-t1
; Γ1; Γ ⊢1 arg1 : in-t1
; ------
; Γ1; Γ ⊢1 fun1 arg1 : out-t1
;
; Γ1, fun1 : in-t1 -> out-t1, x1 : in-t1; Γ ⊢1 def1 : out-t1
; Γ1, fun1 : in-t1 -> out-t1; Γ ⊢1 body1 : t1
; ------
; Γ1; Γ ⊢1 let-fun fun1 x1 = def1 in body1 : t1
;
; ------
; Γ1; Γ ⊢1 zero : Nat1
;
; ------
; Γ1; Γ ⊢1 succ : Nat1 -> Nat1
;
; Γ1; Γ ⊢1 scrut1 : Nat1
; Γ1; Γ ⊢1 zero-branch1 : t1
; Γ1, succ-x1 : Nat1; Γ ⊢1 succ-branch1 : t1
; ------
; Γ1; Γ ⊢1 case-nat scrut1 of
;           { zero -> zero-branch1
;           ; succ succ-x1 -> succ-branch1
;           } : t1
;
; Γ1; Γ ⊢0 lower0 : inner-t
; ------
; Γ1; Γ ⊢1 'lower0 : Dia1 inner-t
;
; Γ1; Γ ⊢1 def1 : Dia1 lower-t
; Γ1; Γ, x0 : lower-t ⊢1 body1 : t1
; ------
; Γ1; Γ ⊢1 let-dia1 x0 = def1 in body1 : t1
(define (check1 gamma1 gamma ee1 tt1)
  (match ee1
    [(mk-var1 x1)
     (unify tt1 (hash-ref gamma1 x1))]
    [(mk-λ1 x1 body1)
     (define x-t1 (new-uf-set))
     (define out-t1 (new-uf-set))
     (and (check1 (hash-set gamma1 x1 x-t1) gamma
                  body1 out-t1)
          (unify tt1 (Arrow1 x-t1 out-t1)))]
    [(mk-app1 fun1 arg1)
     (define in-t1 (new-uf-set))
     (define out-t1 tt1)
     (and (check1 gamma1 gamma fun1 (Arrow1 in-t1 out-t1))
          (check1 gamma1 gamma arg1 in-t1)
          tt1)]
    [(mk-let-fun1 fun1 maybe-t1 x1 def1 body1)
     (define in-t1 (new-uf-set))
     (define out-t1 (new-uf-set))
     (and (when maybe-t1
            (unify maybe-t1 (Arrow1 in-t1 out-t1)))
          (check1 (hash-set* gamma1
                    fun1 (Arrow1 in-t1 out-t1)
                    x1 in-t1)
                  gamma
                  def1 out-t1)
          ; TODO: generalize
          (check1 (hash-set gamma1
                    fun1 (Arrow1 in-t1 out-t1))
                  gamma
                  body1 tt1))]
    [(mk-zero1)
     (unify tt1 (Nat1))]
    [(mk-succ1)
     (unify tt1 (Arrow1 (Nat1) (Nat1)))]
    [(mk-case-nat1 scrut1 zero-branch1 succ-x1 succ-branch1)
     (and (check1 gamma1 gamma scrut1 (Nat1))
          (check1 gamma1 gamma zero-branch1 tt1)
          (check1 (hash-set gamma1 succ-x1 (Nat1)) gamma
                  succ-branch1 tt1))]
    [(mk-quote1 lower0)
     (define lower-t (new-uf-set))
     (and (check0 gamma1 gamma lower0 lower-t)
          (unify tt1 (Dia1 lower-t)))]
    [(mk-let-dia1 x0 maybe-t1 def1 body1)
     (define lower-t (new-uf-set))
     (and (when maybe-t1
            (unify maybe-t1 (Dia1 lower-t)))
          (check1 gamma1 gamma def1 (Dia1 lower-t))
          (check1 gamma1 (hash-set gamma x0 lower-t) body1 tt1))]))
(define (infer1 ee1)
  (define tt1 (new-uf-set))
  (and (check1 (hash) (hash) ee1 tt1)
       (zonk tt1)))

; typing rules for unexpanded phase 0 terms
;
; x0 : t ∈ Γ
; ------
; Γ1; Γ ⊢0 x0 : t
;
; Γ1; Γ, x0 : in-t ⊢0 body0 : out-t
; ------
; Γ1; Γ ⊢0 \x0. body0 : in-t -> out-t
;
; Γ1; Γ ⊢0 fun0 : in-t -> out-t
; Γ1; Γ ⊢0 arg0 : in-t
; ------
; Γ1; Γ ⊢0 fun0 arg0 : out-t
;
; Γ1; Γ, fun0 : in-t -> out-t, x0 : in-t0 ⊢0 def0 : out-t
; Γ1; Γ, fun0 : in-t -> out-t ⊢0 body0 : t
; ------
; Γ1; Γ ⊢0 letfun fun0 x0 = def0 in body0 : t
;
; ------
; Γ1; Γ ⊢0 zero : Nat
;
; ------
; Γ1; Γ ⊢0 succ : Nat -> Nat
;
; Γ1; Γ ⊢0 scrut0 : Nat
; Γ1; Γ ⊢0 zero-branch0 : t
; Γ1; Γ, succ-x0 : Nat ⊢0 succ-branch0 : t
; ------
; Γ1; Γ ⊢0 case-nat scrut0 of
;           { zero -> zero-branch0
;           ; succ succ-x0 -> succ-branch0
;           } : t
;
; Γ1; Γ ⊢1 higher1 : Dia1 lower-t
; ------
; Γ1; Γ ⊢0 $higher1 : lower-t
;
; Γ1; Γ ⊢1 def1 : x-t1
; Γ1, x1 : x-t1; Γ ⊢0 body0 : t
; ------
; Γ1; Γ ⊢0 let-macro0 x1 = def1 in body0 : t
(define (check0 gamma1 gamma ee0 tt)
  (match ee0
    [(mk-var0 x0)
     (unify tt (hash-ref gamma x0))]
    [(mk-λ0 x0 body0)
     (define x-t (new-uf-set))
     (define out-t (new-uf-set))
     (and (check0 gamma1 (hash-set gamma x0 x-t)
                  body0 out-t)
          (unify tt (Arrow x-t out-t)))]
    [(mk-app0 fun0 arg0)
     (define in-t (new-uf-set))
     (define out-t tt)
     (and (check0 gamma1 gamma fun0 (Arrow in-t out-t))
          (check0 gamma1 gamma arg0 in-t)
          tt)]
    [(mk-let-fun0 fun0 maybe-t x0 def0 body0)
     (define in-t (new-uf-set))
     (define out-t (new-uf-set))
     (and (when maybe-t
            (unify maybe-t (Arrow in-t out-t)))
          (check0 gamma1
                  (hash-set* gamma
                    fun0 (Arrow in-t out-t)
                    x0 in-t)
                  def0 out-t)
          ; TODO: generalize
          (check0 gamma1
                  (hash-set gamma
                    fun0 (Arrow in-t out-t))
                  body0 tt))]
    [(mk-zero0)
     (unify tt (Nat))]
    [(mk-succ0)
     (unify tt (Arrow (Nat) (Nat)))]
    [(mk-case-nat0 scrut0 zero-branch0 succ-x0 succ-branch0)
     (and (check0 gamma1 gamma scrut0 (Nat))
          (check0 gamma1 gamma zero-branch0 tt)
          (check0 gamma1 (hash-set gamma succ-x0 (Nat))
                  succ-branch0 tt))]
    [(mk-splice0 higher1)
     (and (check1 gamma1 gamma higher1 (Dia1 tt))
          tt)]
    [(mk-let-macro0 x1 maybe-t1 def1 body0)
     (define def-t1 (new-uf-set))
     (and (when maybe-t1
            (unify maybe-t1 def-t1))
          (check1 gamma1 gamma def1 def-t1)
          (check0 (hash-set gamma1 x1 def-t1) gamma body0 tt))]))
(define (infer0 ee0)
  (define tt (new-uf-set))
  (and (check0 (hash) (hash) ee0 tt)
       (zonk tt)))

; basic examples with infer1
(check-equal? (infer1 (app1 succ1 zero1))
              (Nat1))
(check-equal? (infer1 (app1 zero1 succ1))
              #f)
(check-equal? (infer1 (let-fun1 [(const-zero _) zero1]
                        (app1 const-zero succ1)))
              (Nat1))
(check-equal? (infer1 (let-fun1 [(id x) x]
                        (app1 id zero1)))
              (Nat1))
; TODO: uncomment once generalization is implemented
;(check-equal? (infer1 (let-fun1 "id" "x" (var1 "x")
;                        (app1
;                          (app1 (var1 "id") (var1 "id"))
;                          (zero1))))
;              (Nat1))
(check-equal? (infer1 (let-fun1 [(add x y)
                                 (case-nat1 x
                                   [zero1
                                    y]
                                   [(succ1 x-1)
                                    (app1 succ1
                                      (app1 add x-1 y))])]
                        (app1 add (nat1 2) (nat1 2))))
              (Nat1))
; same basic examples with infer0
(check-equal? (infer0 (app0 succ0 zero0))
              (Nat))
(check-equal? (infer0 (app0 zero0 succ0))
              #f)
(check-equal? (infer0 (let-fun0 [(const-zero _) zero0]
                        (app0 const-zero succ0)))
              (Nat))
(check-equal? (infer0 (let-fun0 [(id x) x]
                        (app0 id zero0)))
              (Nat))
; TODO: uncomment once generalization is implemented
;(check-equal? (infer0 (let-fun0 "id" "x" (var0 "x")
;                        (app0
;                          (app0 (var0 "id") (var0 "id"))
;                          (zero0))))
;              (Nat))
(check-equal? (infer0 (let-fun0 [(add x y)
                                 (case-nat0 x
                                   [zero0
                                    y]
                                   [(succ0 x-1)
                                    (app0 succ0
                                      (app0 add x-1 y))])]
                        (app0 add (nat0 2) (nat0 2))))
              (Nat))
; more interesting examples with let-dia1, quote1, let-macro0, and splice0:
(check-equal? (infer1 (let-dia1 [two (quote1 (nat0 2))]
                        (quote1 (app0 succ0
                                  (app0 succ0
                                    two)))))
              (Dia1 (Nat)))
(check-equal? (infer0 (let-fun0 [(add x y)
                                 (case-nat0 x
                                   [zero0
                                    y]
                                   [(succ0 x-1)
                                    (app0 succ0
                                      (app0 add x-1 y))])]
                        (let-fun0 [(mul x y)
                                   (case-nat0 x
                                     [zero0
                                      zero0]
                                     [(succ0 x-1)
                                      (app0 add
                                        y
                                        (app0 mul x-1 y))])]
                          (let-macro0 [(power n diaX)
                                       (let-dia1 [x diaX]
                                         (let-fun1 [(go n-1)
                                                    (case-nat1 n-1
                                                      [zero1
                                                       (quote1 x)]
                                                      [(succ1 n-2)
                                                       (let-dia1 [recur
                                                                  (app1 go n-2)]
                                                         (quote1
                                                           (app0 mul x recur)))])]
                                           (case-nat1 n
                                             [zero1
                                              (quote1 (nat0 1))]
                                             [(succ1 n-1)
                                              (app1 go n-1)])))]
                            (let-fun0 [(square x)
                                       (splice0 (app1 power (nat1 2) (quote1 x)))]
                              (app0 square (app0 square (nat0 2))))))))
              (Nat))

; typing rules for expanded phase 0 terms
;
; x : t ∈ Γ
; ------
; Γ ⊢ x : t
;
; Γ, x : in-t ⊢ body : out-t
; ------
; Γ ⊢ \x. body : in-t -> out-t
;
; Γ ⊢ fun : in-t -> out-t
; Γ ⊢ arg : in-t
; ------
; Γ ⊢ fun arg : out-t
;
; Γ, fun : in-t -> out-t, x : in-t ⊢ def : out-t
; Γ, fun : in-t -> out-t ⊢ body : t
; ------
; Γ ⊢ let-fun fun x = def in body : t
;
; ------
; Γ ⊢ zero : Nat
;
; ------
; Γ ⊢ succ : Nat -> Nat
;
; Γ ⊢ scrut : Nat
; Γ ⊢ zero-branch : t
; Γ, succ-x : Nat ⊢ succ-branch : t
; ------
; Γ ⊢ case-nat scrut of
;       { zero -> zero-branch
;       ; succ succ-x -> succ-branch
;       } : t
(define (check gamma ee tt)
  (match ee
    [(mk-var x)
     (unify tt (hash-ref gamma x))]
    [(mk-λ x body)
     (define x-t (new-uf-set))
     (define out-t (new-uf-set))
     (and (check (hash-set gamma x x-t)
                  body out-t)
          (unify tt (Arrow x-t out-t)))]
    [(mk-app fun arg)
     (define in-t (new-uf-set))
     (define out-t tt)
     (and (check gamma fun (Arrow in-t out-t))
          (check gamma arg in-t)
          tt)]
    [(mk-let-fun fun maybe-t x def body)
     (define in-t (new-uf-set))
     (define out-t (new-uf-set))
     (and (when maybe-t
            (unify maybe-t (Arrow in-t out-t)))
          (check (hash-set* gamma
                    fun (Arrow in-t out-t)
                    x in-t)
                  def out-t)
          ; TODO: generalize
          (check (hash-set gamma
                    fun (Arrow in-t out-t))
                  body tt))]
    [(mk-zero)
     (unify tt (Nat))]
    [(mk-succ)
     (unify tt (Arrow (Nat) (Nat)))]
    [(mk-case-nat scrut zero-branch succ-x succ-branch)
     (and (check gamma scrut (Nat))
          (check gamma zero-branch tt)
          (check (hash-set gamma succ-x (Nat))
                  succ-branch tt))]))
(define (infer ee)
  (define tt (new-uf-set))
  (and (check (hash) ee tt)
       (zonk tt)))
; same basic examples with infer
(check-equal? (infer (app succ zero))
              (Nat))
(check-equal? (infer (app zero succ))
              #f)
(check-equal? (infer (let-fun [(const-zero _) zero]
                        (app const-zero succ)))
              (Nat))
(check-equal? (infer (let-fun [(id x) x]
                        (app id zero)))
              (Nat))
; TODO: uncomment once generalization is implemented
;(check-equal? (infer (let-fun "id" "x" (var "x")
;                        (app
;                          (app (var "id") (var "id"))
;                          (zero))))
;              (Nat))
(check-equal? (infer (let-fun [(add x y)
                                 (case-nat x
                                   [zero
                                    y]
                                   [(succ x-1)
                                    (app succ
                                      (app add x-1 y))])]
                        (app add (nat 2) (nat 2))))
              (Nat))


;;;;;;;;;;;;;;;
; interpreter ;
;;;;;;;;;;;;;;;

; big-steps semantics for phase 1 terms. note that
;
;   Γ1; {σ} ⊢ e0 => e
;
; is expansion, not evaluation, and that σ maps variables to expanded terms,
; not to values.
;
; x1 ↦ v1 ∈ Γ1
; ------
; Γ1; σ ⊢ x1 => v1
;
; ------
; Γ1; σ ⊢ \x1. body1 => clo Γ1 σ x1 body1
;
; Γ1; σ ⊢ fun1 => clo clo-Γ1 σ x1 body1
; Γ1; σ ⊢ arg1 => in1
; clo-Γ1, x1 ↦ in1; clo-σ ⊢ body1 => out1
; ------
; Γ1; σ ⊢ fun1 arg2 => out1
;
; ext-Γ1@{Γ1, fun1 ↦ clo ext-Γ1 σ x1 def1}; σ ⊢ body1 => v1
; ------
; Γ1; σ ⊢ let-fun fun1 x1 = def1 in body1 => v1
;
; ------
; Γ1; σ ⊢ zero => zero
;
; ------
; Γ1; σ ⊢ succ => succ
;
; Γ1; σ ⊢ fun1 => succ
; Γ1; σ ⊢ arg1 => n1
; ------
; Γ1; σ ⊢ fun1 arg2 => succ n1
;
; Γ1; σ ⊢ scrut1 => zero
; Γ1; σ ⊢ zero-branch1 => v1
; ------
; Γ1; σ ⊢ case-nat scrut1 of
;           { zero -> zero-branch1
;           ; succ succ-x1 -> succ-branch1
;           }
;      => v1
;
; Γ1; σ ⊢ scrut1 => succ n1
; Γ1, succ-x1 ↦ n1; σ ⊢ succ-branch1 => v1
; ------
; Γ1; σ ⊢ case-nat scrut1 of
;           { zero -> zero-branch1
;           ; succ succ-x1 -> succ-branch1
;           }
;      => v1
;
; Γ1; {σ} ⊢ lower0 => lower
; ------
; Γ1; σ ⊢ 'lower0 => 'lower
;
; Γ1; σ ⊢ def1 => 'lower
; Γ1; Γ, x0 ↦ lower ⊢ body1 => v1
; ------
; Γ1; σ ⊢ let-dia1 x0 = def1 in body
(struct clo-val1 (gamma1 sigma x1 body1) #:transparent)
(struct succ-val1 () #:transparent)
(struct nat-val1 (n) #:transparent)
(struct quoted-val1 (expr) #:transparent)
(define (eval1 gamma1 sigma ee1)
  (match ee1
    [(mk-var1 x1)
     ((hash-ref gamma1 x1))]
    [(mk-λ1 x1 body1)
     (clo-val1 gamma1 sigma x1 body1)]
    [(mk-app1 fun1 arg1)
     (match (eval1 gamma1 sigma fun1)
       [(clo-val1 clo-gamma1 clo-sigma x1 body1)
        (define in1 (eval1 gamma1 sigma arg1))
        (eval1 (hash-set clo-gamma1 x1 (lambda () in1)) clo-sigma body1)]
       [(succ-val1)
        (match (eval1 gamma1 sigma arg1)
          [(nat-val1 in1)
           (nat-val1 (+ in1 1))])])]
    [(mk-let-fun1 fun1 _maybe-t1 x1 def1 body1)
     (define (mk-fun)
       (clo-val1 (hash-set gamma1 fun1 mk-fun) sigma x1 def1))
     (eval1 (hash-set gamma1 fun1 mk-fun) sigma body1)]
    [(mk-zero1)
     (nat-val1 0)]
    [(mk-succ1)
     (succ-val1)]
    [(mk-case-nat1 scrut1 zero-branch1 succ-x1 succ-branch1)
     (match (eval1 gamma1 sigma scrut1)
       [(nat-val1 0)
        (eval1 gamma1 sigma zero-branch1)]
       [(nat-val1 n)
        (define x (nat-val1 (- n 1)))
        (eval1 (hash-set gamma1 succ-x1 (lambda () x)) sigma succ-branch1)])]
    [(mk-quote1 lower0)
     (quoted-val1 (expand0 gamma1 sigma lower0))]
    [(mk-let-dia1 x0 _maybe-t1 def1 body1)
     (match (eval1 gamma1 sigma def1)
       [(quoted-val1 lower)
        (eval1 gamma1 (hash-set sigma x0 lower) body1)])]))
(define (eval-closed1 ee1)
  (eval1 (hash) (hash) ee1))

; big-steps semantics for expanding unexpanded phase 0 terms
;
; x0 ↦ e ∈ σ
; ------
; Γ1; {σ} ⊢ x0 => e
;
; Γ1; {σ, x0 ↦ x} ⊢ body0 => body
; ------
; Γ1; {σ} ⊢ \x0. body0 => \x. body
;
; Γ1; {σ} ⊢ fun0 => fun
; Γ1; {σ} ⊢ arg0 => arg
; ------
; Γ1; {σ} ⊢ fun0 arg0 => fun arg
;
; Γ1; {σ, fun0 ↦ fun, x0 ↦ x} ⊢ def0 => def
; Γ1; {σ, fun0 ↦ fun} ⊢ body0 => body
; ------
; Γ1; {σ} ⊢ let-fun fun0 x0 = def0 in body0
;        => let-fun fun x = def in body
;
; ------
; Γ1; {σ} ⊢ zero0 => zero
;
; ------
; Γ1; {σ} ⊢ succ0 => succ
;
; Γ1; {σ} ⊢ scrut0 => scrut
; Γ1; {σ} ⊢ zero-branch0 => zero-branch
; Γ1; {σ, succ-x0 ↦ succ-x} ⊢ succ-branch0 => succ-branch
; ------
; Γ1; {σ} ⊢ case-nat0 scrut0 of
;             { zero -> zero-branch0
;             ; succ succ-x0 -> succ-branch0
;             }
;        => case-nat scrut of
;            { zero -> zero-branch
;            ; succ succ-x -> succ-branch
;            }
;
; {Γ1}; σ ⊢ higher1 => 'lower
; ------
; Γ1; {σ} ⊢ $higher1 => lower
;
; {Γ1}; σ ⊢ def1 => v1
; Γ1, x0 ↦ v1; {σ} ⊢ body0 => body
; ------
; Γ1; {σ} ⊢ let-macro1 x0 = def1 in body0 => body
(define (expand0 gamma1 sigma ee0)
  (match ee0
    [(mk-var0 x0)
     (hash-ref sigma x0)]
    [(mk-λ0 x0 body0)
     (define body (expand0 gamma1 (hash-set sigma
                                    x0 (mk-var x0))
                            body0))
     (mk-λ x0 body)]
    [(mk-app0 fun0 arg0)
     (define fun (expand0 gamma1 sigma fun0))
     (define arg (expand0 gamma1 sigma arg0))
     (mk-app fun arg)]
    [(mk-let-fun0 fun0 maybe-t x0 def0 body0)
     (define def (expand0 gamma1 (hash-set* sigma
                                   fun0 (mk-var fun0)
                                   x0 (mk-var x0))
                           def0))
     (define body (expand0 gamma1 (hash-set sigma
                                    fun0 (mk-var fun0))
                            body0))
     (mk-let-fun fun0 maybe-t x0 def body)]
    [(mk-zero0)
     (mk-zero)]
    [(mk-succ0)
     (mk-succ)]
    [(mk-case-nat0 scrut0 zero-branch0 succ-x0 succ-branch0)
     (define scrut (expand0 gamma1 sigma scrut0))
     (define zero-branch (expand0 gamma1 sigma zero-branch0))
     (define succ-branch (expand0 gamma1 (hash-set sigma
                                           succ-x0 (mk-var succ-x0))
                                   succ-branch0))
     (mk-case-nat scrut zero-branch succ-x0 succ-branch)]
    [(mk-splice0 higher1)
     (match (eval1 gamma1 sigma higher1)
       [(quoted-val1 lower)
        lower])]
    [(mk-let-macro0 x0 _maybe-t1 def1 body0)
     (define v1 (eval1 gamma1 sigma def1))
     (expand0 (hash-set gamma1 x0 (lambda () v1)) sigma
              body0)]))
(define (expand-closed0 ee0)
  (expand0 (hash) (hash) ee0))
; the usual basic examples, with eval1
(check-equal? (eval-closed1 (app1 succ1 zero1))
              (nat-val1 1))
; TODO: throw and catch runtime errors
;(check-equal? (eval-closed1 (app1 zero1 succ1))
;              #f)
(check-equal? (eval-closed1 (let-fun1 [(const-zero _) zero1]
                              (app1 const-zero succ1)))
              (nat-val1 0))
(check-equal? (eval-closed1 (let-fun1 [(id x) x]
                              (app1 id zero1)))
              (nat-val1 0))
(check-equal? (eval-closed1 (let-fun1 [(id x) x]
                              (app1 id id zero1)))
              (nat-val1 0))
(check-equal? (eval-closed1 (let-fun1 [(add x y)
                                       (case-nat1 x
                                         [zero1
                                          y]
                                         [(succ1 x-1)
                                          (app1 succ1
                                            (app1 add x-1 y))])]
                              (app1 add (nat1 2) (nat1 2))))
              (nat-val1 4))
; more interesting examples with let-dia1, quote1, let-macro0, and splice0:
(check-equal? (eval-closed1 (let-dia1 [two (quote1 (nat0 2))]
                              (quote1 (app0 succ0
                                        (app0 succ0
                                          two)))))
              (quoted-val1 (nat 4)))
(check-equal? (expand-closed0 (let-fun0 [(add x y)
                                         (case-nat0 x
                                           [zero0
                                            y]
                                           [(succ0 x-1)
                                            (app0 succ0
                                              (app0 add x-1 y))])]
                                (let-fun0 [(mul x y)
                                           (case-nat0 x
                                             [zero0
                                              zero0]
                                             [(succ0 x-1)
                                              (app0 add
                                                y
                                                (app0 mul x-1 y))])]
                                  (let-macro0 [(power n diaX)
                                               (let-dia1 [x diaX]
                                                 (let-fun1 [(go n-1)
                                                            (case-nat1 n-1
                                                              [zero1
                                                               (quote1 x)]
                                                              [(succ1 n-2)
                                                               (let-dia1 [recur
                                                                          (app1 go n-2)]
                                                                 (quote1
                                                                   (app0 mul x recur)))])]
                                                   (case-nat1 n
                                                     [zero1
                                                      (quote1 (nat0 1))]
                                                     [(succ1 n-1)
                                                      (app1 go n-1)])))]
                                    (let-fun0 [(square x)
                                               (splice0 (app1 power
                                                              (nat1 2)
                                                              (quote1 x)))]
                                      (app0 square (app0 square (nat0 2))))))))
              (let-fun [(add x) (λ (y)
                                   (case-nat x
                                     [zero
                                      y]
                                     [(succ x-1)
                                      (app succ
                                        (app add x-1 y))]))]
                (let-fun [(mul x) (λ (y)
                                     (case-nat x
                                       [zero
                                        zero]
                                       [(succ x-1)
                                        (app add
                                          y
                                          (app mul x-1 y))]))]
                  (let-fun [(square x)
                             (app mul x x)]
                    (app square
                      (app square
                        (nat 2)))))))

; big steps semantics for expanded phase 0 terms
;
; x ↦ v ∈ Γ
; ------
; Γ ⊢ x => v
;
; ------
; Γ ⊢ \x. body => clo Γ x body
;
; Γ ⊢ fun => clo clo-Γ x def
; Γ ⊢ arg => in
; clo-Γ, x ↦ in ⊢ body => out
; ------
; Γ ⊢ fun arg => out
;
; ext-Γ@(Γ, fun ↦ clo ext-Γ x def); Γ ⊢ body => v
; ------
; Γ ⊢ let-fun fun x = def in body => v
;
; ------
; Γ ⊢ zero => zero
;
; ------
; Γ ⊢ succ => succ
;
; Γ ⊢ fun => succ
; Γ ⊢ arg => n
; ------
; Γ ⊢ fun arg => succ n
;
; Γ ⊢ scrut => zero
; Γ ⊢ zero-branch => v
; ------
; Γ ⊢ case-nat scrut of
;       { zero -> zero-branch
;       ; succ succ-x -> succ-branch
;       }
;  => v
;
; Γ ⊢ scrut => succ n
; Γ, succ-x ↦ n ⊢ succ-branch => v
; ------
; Γ ⊢ case-nat scrut of
;       { zero -> zero-branch
;       ; succ succ-x -> succ-branch
;       }
;  => v
(struct clo-val (gamma x body) #:transparent)
(struct succ-val () #:transparent)
(struct nat-val (n) #:transparent)
(define (eval gamma ee)
  (match ee
    [(mk-var x)
     ((hash-ref gamma x))]
    [(mk-λ x body)
     (clo-val gamma x body)]
    [(mk-app fun arg)
     (match (eval gamma fun)
       [(clo-val clo-gamma x body)
        (define in (eval gamma arg))
        (eval (hash-set clo-gamma x (lambda () in)) body)]
       [(succ-val)
        (match (eval gamma arg)
          [(nat-val n)
           (nat-val (+ n 1))])])]
    [(mk-let-fun fun _maybe-t x def body)
     (define (mk-fun)
       (clo-val (hash-set gamma fun mk-fun) x def))
     (eval (hash-set gamma fun mk-fun) body)]
    [(mk-zero)
     (nat-val 0)]
    [(mk-succ)
     (succ-val)]
    [(mk-case-nat scrut zero-branch succ-x succ-branch)
     (match (eval gamma scrut)
       [(nat-val 0)
        (eval gamma zero-branch)]
       [(nat-val n)
        (define x (nat-val (- n 1)))
        (eval (hash-set gamma succ-x (lambda () x)) succ-branch)])]))
(define (eval-closed ee)
  (eval (hash) ee))
; the usual basic examples, with eval
(check-equal? (eval-closed (app succ zero))
              (nat-val 1))
; TODO: throw and catch runtime errors
;(check-equal? (eval-closed (app zero succ))
;              #f)
(check-equal? (eval-closed (let-fun [(const-zero _) zero]
                              (app const-zero succ)))
              (nat-val 0))
(check-equal? (eval-closed (let-fun [(id x) x]
                              (app id zero)))
              (nat-val 0))
(check-equal? (eval-closed (let-fun [(id x) x]
                              (app id id zero)))
              (nat-val 0))
(check-equal? (eval-closed (let-fun [(add x y)
                                       (case-nat x
                                         [zero
                                          y]
                                         [(succ x-1)
                                          (app succ
                                            (app add x-1 y))])]
                              (app add (nat 2) (nat 2))))
              (nat-val 4))
