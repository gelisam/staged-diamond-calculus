#lang racket
(require rackunit)
(require data/union-find)

;;;;;;;;;;;;;
; utilities ;
;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;
; raw syntax ;
;;;;;;;;;;;;;;

; phase 1 (*M*acro-level) terms with phase 0 terms inside of them
; eM ::= xM | \xM. eM | eM eM
;      | zero | succ | case-nat eM of {zero -> eM; succ xM -> eM}
;      | 'eU | let-diaM xU = eM in eM
(struct mk-varM (xM) #:transparent)
(struct mk-λM (xM bodyM) #:transparent)
(struct mk-appM (funM argM) #:transparent)
(struct mk-let-funM (funM maybe-tM xM defM bodyM) #:transparent)
(struct mk-zeroM () #:transparent)
(struct mk-succM () #:transparent)
(struct mk-case-natM (scrutM zero-branchM succ-xM succ-branchM) #:transparent)
(struct mk-quoteM (lowerU) #:transparent)
(struct mk-let-diaM (xU maybe-tM defM bodyM) #:transparent)

; *U*nexpanded phase 0 terms with phase 1 terms inside of them
; eU ::= xU | \xU. eU | eU eU
;      | zero | succ | case-nat eU of {zero -> eU; succ xU -> eU}
;      | $eM | let-macroU xM = eM in eU
(struct mk-varU (xU) #:transparent)
(struct mk-λU (xU bodyU) #:transparent)
(struct mk-appU (funU argU) #:transparent)
(struct mk-let-funU (funU maybe-tZ xU defU bodyU) #:transparent)
(struct mk-zeroU () #:transparent)
(struct mk-succU () #:transparent)
(struct mk-case-natU (scrutU zero-branchU succ-xU succ-branchU) #:transparent)
(struct mk-spliceU (termM) #:transparent)
(struct mk-let-macroU (xM maybe-tM defM bodyU) #:transparent)

; *E*xpanded phase 0 terms, with no phase 1 terms
; eE ::= xE | \xE. eE | eE eE
;      | zero | succ | case-nat eE of {zero -> eE; succ x -> eE}
(struct mk-varE (xE) #:transparent)
(struct mk-λE (xE bodyE) #:transparent)
(struct mk-appE (funE argE) #:transparent)
(struct mk-let-funE (funE maybe-tZ xE defE bodyE) #:transparent)
(struct mk-zeroE () #:transparent)
(struct mk-succE () #:transparent)
(struct mk-case-natE (scrutE zero-branchE succ-xE succ-branchE) #:transparent)


; phase 1 (*M*acro-level) types with phase 0 types inside of them
; tM ::= tM -> tM | NatM | Dia tZ
(struct ArrowM (in-tM out-tM) #:transparent)
(struct NatM () #:transparent)
(struct DiaM (lower-tZ) #:transparent)

; phase 0 (*Z*ero) types with no phase 1 types
; tZ ::= tZ -> tZ | NatZ
(struct ArrowZ (in-tZ out-tZ) #:transparent)
(struct NatZ () #:transparent)


;;;;;;;;;;;;;;;;;;;
; syntactic sugar ;
;;;;;;;;;;;;;;;;;;;

; basic syntax sugar for Macro-level phase 1 terms

(define-syntax-rule (λM1 x body)
  (mk-λM 'x
    (let ([x (mk-varM 'x)])
      body)))
(check-equal? (λM1 xM xM)
              (mk-λM 'xM (mk-varM 'xM)))

(define-syntax (λM stx)
  (syntax-case stx ()
    [(_ () bodyM)
     #'bodyM]
    [(_ (x xs ...) bodyM)
     #'(λM1 x (λM (xs ...) bodyM))]))
(check-equal? (λM (xM yM) xM)
              (mk-λM 'xM
                (mk-λM 'yM
                  (mk-varM 'xM))))

(define-syntax (appM stx)
  (syntax-case stx ()
    [(_ funM argM)
     #'(mk-appM funM argM)]
    [(_ funM argMs ... argM)
     #'(mk-appM (appM funM argMs ...) argM)]))
(check-equal? (appM (mk-varM 'f) (mk-varM 'x) (mk-varM 'y) (mk-varM 'z))
              (mk-appM
                (mk-appM
                  (mk-appM
                    (mk-varM 'f)
                    (mk-varM 'x))
                  (mk-varM 'y))
                (mk-varM 'z)))

(define-syntax (let-funM stx)
  (syntax-case stx ()
    [(_ [(fun x y ...) def] body)
     #'(mk-let-funM 'fun #f 'x
         (let ([fun (mk-varM 'fun)]
               [x (mk-varM 'x)])
           (λM (y ...) def))
         (let ([fun (mk-varM 'fun)])
           body))]))
(check-equal? (let-funM [(f x) (appM f x)]
                (appM f (mk-zeroM)))
              (mk-let-funM 'f #f 'x
                (mk-appM (mk-varM 'f) (mk-varM 'x))
                (mk-appM (mk-varM 'f) (mk-zeroM))))
(check-equal? (let-funM [(f x y) (appM f x y)]
                (appM f (mk-zeroM) (mk-zeroM)))
              (mk-let-funM 'f #f 'x
                (mk-λM 'y (appM (mk-varM 'f) (mk-varM 'x) (mk-varM 'y)))
                (appM (mk-varM 'f) (mk-zeroM) (mk-zeroM))))

(define zeroM (mk-zeroM))
(define succM (mk-succM))

(define (natM n)
  (if (zero? n)
      zeroM
      (appM succM (natM (- n 1)))))

(define-syntax case-natM
  (syntax-rules (zeroM succM)
    [(_ scrutM [zeroM zero-branchM] [(succM x) succ-branchM])
     (mk-case-natM scrutM
       zero-branchM
       'x (let ([x (mk-varM 'x)])
            succ-branchM))]))
(check-equal? (case-natM zeroM
                [zeroM
                 zeroM]
                [(succM xM)
                 (appM succM xM)])
              (mk-case-natM (mk-zeroM)
                (mk-zeroM)
                'xM (mk-appM (mk-succM) (mk-varM 'xM))))

; basic syntax sugar for Unexpanded phase 0 terms

(define-syntax-rule (λU1 x body)
  (mk-λU 'x
    (let ([x (mk-varU 'x)])
      body)))
(check-equal? (λU1 xU xU)
              (mk-λU 'xU (mk-varU 'xU)))

(define-syntax (λU stx)
  (syntax-case stx ()
    [(_ () bodyU)
     #'bodyU]
    [(_ (x xs ...) bodyU)
     #'(λU1 x (λU (xs ...) bodyU))]))
(check-equal? (λU (xU yU) xU)
              (mk-λU 'xU
                (mk-λU 'yU
                  (mk-varU 'xU))))

(define-syntax (appU stx)
  (syntax-case stx ()
    [(_ funU argU)
     #'(mk-appU funU argU)]
    [(_ funU argUs ... argU)
     #'(mk-appU (appU funU argUs ...) argU)]))
(check-equal? (appU (mk-varU 'f) (mk-varU 'x) (mk-varU 'y) (mk-varU 'z))
              (mk-appU
                (mk-appU
                  (mk-appU
                    (mk-varU 'f)
                    (mk-varU 'x))
                  (mk-varU 'y))
                (mk-varU 'z)))

(define-syntax (let-funU stx)
  (syntax-case stx ()
    [(_ [(fun x y ...) def] body)
     #'(mk-let-funU 'fun #f 'x
         (let ([fun (mk-varU 'fun)]
               [x (mk-varU 'x)])
           (λU (y ...) def))
         (let ([fun (mk-varU 'fun)])
           body))]))
(check-equal? (let-funU [(f x) (appU f x)]
                (appU f (mk-zeroU)))
              (mk-let-funU 'f #f 'x
                (mk-appU (mk-varU 'f) (mk-varU 'x))
                (mk-appU (mk-varU 'f) (mk-zeroU))))
(check-equal? (let-funU [(f x y) (appU f x y)]
                (appU f (mk-zeroU) (mk-zeroU)))
              (mk-let-funU 'f #f 'x
                (mk-λU 'y (appU (mk-varU 'f) (mk-varU 'x) (mk-varU 'y)))
                (appU (mk-varU 'f) (mk-zeroU) (mk-zeroU))))

(define zeroU (mk-zeroU))
(define succU (mk-succU))

(define (natU n)
  (if (zero? n)
      zeroU
      (appU succU (natU (- n 1)))))

(define-syntax case-natU
  (syntax-rules (zeroU succU)
    [(_ scrutU [zeroU zero-branchU] [(succU x) succ-branchU])
     (mk-case-natU scrutU
       zero-branchU
       'x (let ([x (mk-varU 'x)])
            succ-branchU))]))
(check-equal? (case-natU zeroU
                [zeroU
                 zeroU]
                [(succU xU)
                 (appU succU xU)])
              (mk-case-natU (mk-zeroU)
                (mk-zeroU)
                'xU (mk-appU (mk-succU) (mk-varU 'xU))))

; basic syntax sugar for Expanded phase 0 terms

(define-syntax-rule (λE1 x body)
  (mk-λE 'x
    (let ([x (mk-varE 'x)])
      body)))
(check-equal? (λE1 xE xE)
              (mk-λE 'xE (mk-varE 'xE)))

(define-syntax (λE stx)
  (syntax-case stx ()
    [(_ () bodyE)
     #'bodyE]
    [(_ (x xs ...) bodyE)
     #'(λE1 x (λE (xs ...) bodyE))]))
(check-equal? (λE (xE yE) xE)
              (mk-λE 'xE
                (mk-λE 'yE
                  (mk-varE 'xE))))

(define-syntax (appE stx)
  (syntax-case stx ()
    [(_ funE argE)
     #'(mk-appE funE argE)]
    [(_ funE argEs ... argE)
     #'(mk-appE (appE funE argEs ...) argE)]))
(check-equal? (appE (mk-varE 'f) (mk-varE 'x) (mk-varE 'y) (mk-varE 'z))
              (mk-appE
                (mk-appE
                  (mk-appE
                    (mk-varE 'f)
                    (mk-varE 'x))
                  (mk-varE 'y))
                (mk-varE 'z)))

(define-syntax (let-funE stx)
  (syntax-case stx ()
    [(_ [(fun x y ...) def] body)
     #'(mk-let-funE 'fun #f 'x
         (let ([fun (mk-varE 'fun)]
               [x (mk-varE 'x)])
           (λE (y ...) def))
         (let ([fun (mk-varE 'fun)])
           body))]))
(check-equal? (let-funE [(f x) (appE f x)]
                (appE f (mk-zeroE)))
              (mk-let-funE 'f #f 'x
                (mk-appE (mk-varE 'f) (mk-varE 'x))
                (mk-appE (mk-varE 'f) (mk-zeroE))))
(check-equal? (let-funE [(f x y) (appE f x y)]
                (appE f (mk-zeroE) (mk-zeroE)))
              (mk-let-funE 'f #f 'x
                (mk-λE 'y (appE (mk-varE 'f) (mk-varE 'x) (mk-varE 'y)))
                (appE (mk-varE 'f) (mk-zeroE) (mk-zeroE))))

(define zeroE (mk-zeroE))
(define succE (mk-succE))

(define (natE n)
  (if (zero? n)
      zeroE
      (appE succE (natE (- n 1)))))

(define-syntax case-natE
  (syntax-rules (zeroE succE)
    [(_ scrutE [zeroE zero-branchE] [(succE x) succ-branchE])
     (mk-case-natE scrutE
       zero-branchE
       'x (let ([x (mk-varE 'x)])
            succ-branchE))]))
(check-equal? (case-natE zeroE
                [zeroE
                 zeroE]
                [(succE xE)
                 (appE succE xE)])
              (mk-case-natE (mk-zeroE)
                (mk-zeroE)
                'xE (mk-appE (mk-succE) (mk-varE 'xE))))

; more interesting syntax sugar with let-diaM, quoteM, let-macroU, and spliceU

(define-syntax-rule (let-diaM [x defM] bodyM)
  (mk-let-diaM 'x #f defM
    (let ([x (mk-varU 'x)])
      bodyM)))
(define (quoteM bodyU) (mk-quoteM bodyU))
(check-equal? (let-diaM [one (natU 1)]
                (quoteM (appU one zeroU)))
              (mk-let-diaM 'one #f (mk-appU (mk-succU) (mk-zeroU))
                (mk-quoteM (mk-appU (mk-varU 'one) (mk-zeroU)))))

(define-syntax-rule (let-macroU1 [x defM] bodyU)
  (mk-let-macroU 'x #f defM
    (let ([x (mk-varM 'x)])
      bodyU)))
(define-syntax (let-macroU stx)
  (syntax-case stx ()
    [(_ [(f x ...) defM] bodyU)
     #'(let-macroU1 [f (λM (x ...) defM)] bodyU)]
    [(_ [f defM] bodyU)
     #'(let-macroU1 [f defM] bodyU)]))
(define (spliceU termM) (mk-spliceU termM))
(check-equal? (let-macroU [one (natM 1)]
                (spliceU (appM (mk-varU 'f) one)))
              (mk-let-macroU 'one #f (mk-appM (mk-succM) (mk-zeroM))
                (mk-spliceU (mk-appM (mk-varU 'f) (mk-varM 'one)))))
(check-equal? (let-macroU [(f x) (appM succM x)]
                (spliceU (appM f (quoteM (mk-varM 'one)))))
              (mk-let-macroU 'f #f (mk-λM 'x (mk-appM (mk-succM) (mk-varM 'x)))
                (mk-spliceU (mk-appM (mk-varM 'f) (mk-quoteM (mk-varM 'one))))))


;;;;;;;;;;;;;;;
; unification ;
;;;;;;;;;;;;;;;

(define (new-uf-set)
  (uf-new #f))

(define (occurs? uf-set t)
  (match t
    [(? uf-set? other-uf-set)
     (uf-same-set? uf-set other-uf-set)]
    [(ArrowM ta tb)
     (or (occurs? uf-set ta)
         (occurs? uf-set tb))]
    [(ArrowZ ta tb)
     (or (occurs? uf-set ta)
         (occurs? uf-set tb))]
    [(NatM) #f]
    [(NatZ) #f]
    [(DiaM t)
     (occurs? uf-set t)]))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)])
  (check-equal? (occurs? uf-set-a (ArrowM (NatM) (NatM))) #f)
  (check-equal? (occurs? uf-set-a (ArrowM (NatM) uf-set-a)) #t)
  (check-equal? (occurs? uf-set-a (ArrowM (NatM) uf-set-b)) #f))

(define (zonk1 t)
  (if (uf-set? t)
      (or (uf-find t)
          t)
      t))
(define (zonk t)
  (match (zonk1 t)
    [(? uf-set? uf-set)
     uf-set]
    [(ArrowM in-t out-t)
     (ArrowM (zonk in-t)
             (zonk out-t))]
    [(ArrowZ in-t out-t)
     (ArrowZ (zonk in-t)
             (zonk out-t))]
    [(NatM)
     (NatM)]
    [(NatZ)
     (NatZ)]
    [(DiaM lower-t)
     (DiaM (zonk lower-t))]))

(define (equivalent? ta tb)
  (let ([zonked1-ta (zonk1 ta)]
        [zonked1-tb (zonk1 tb)])
    (match (list zonked1-ta zonked1-tb)
      [(list (? uf-set? uf-set-a)
             (? uf-set? uf-set-b))
       (uf-same-set? uf-set-a uf-set-b)]
      [(list (ArrowM in-a out-a)
             (ArrowM in-b out-b))
       (and (equivalent? in-a in-b)
            (equivalent? out-a out-b))]
      [(list (ArrowZ in-a out-a)
             (ArrowZ in-b out-b))
       (and (equivalent? in-a in-b)
            (equivalent? out-a out-b))]
      [(list (NatM)
             (NatM))
       #t]
      [(list (NatZ)
             (NatZ))
       #t]
      [(list (DiaM lower-ta)
             (DiaM lower-tb))
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
      [(list (ArrowM in-a out-a)
             (ArrowM in-b out-b))
       (and-let* ([in (unify in-a in-b)]
                  [out (unify out-a out-b)])
         (ArrowM in out))]
      [(list (ArrowZ in-a out-a)
             (ArrowZ in-b out-b))
       (and-let* ([in (unify in-a in-b)]
                  [out (unify out-a out-b)])
         (ArrowZ in out))]
      [(list (NatM)
             (NatM))
       (NatM)]
      [(list (NatZ)
             (NatZ))
       (NatZ)]
      [(list (DiaM lower-ta)
             (DiaM lower-tb))
       (and-let* ([lower (unify lower-ta lower-tb)])
         (DiaM lower))]
      [_
       #f])))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)])
  (check-equal? (unify (ArrowM (NatM) (NatM))
                       (NatM))
                #f)
  (check-equal? (unify (ArrowM (NatM) (NatM))
                       (ArrowM (NatM) (NatM)))
                (ArrowM (NatM) (NatM)))
  (check-equal? (unify (ArrowM uf-set-a (NatM))
                       (ArrowM (NatM) uf-set-b))
                (ArrowM (NatM) (NatM)))
  (check-equal? (zonk1 uf-set-a) (NatM))
  (check-equal? (zonk1 uf-set-b) (NatM)))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)])
  (check-equal? (uf-same-set? uf-set-a uf-set-b)
                #f)
  (check-equal? (equivalent?
                  (unify (ArrowM uf-set-a uf-set-b)
                         (ArrowM uf-set-b uf-set-a))
                  (ArrowM uf-set-a uf-set-a))
                #t))
(let ([uf-set-a (new-uf-set)]
      [uf-set-b (new-uf-set)]
      [uf-set-c (new-uf-set)]
      [uf-set-d (new-uf-set)])
  (check-equal? (equivalent?
                  (unify (ArrowM uf-set-a uf-set-b)
                         (ArrowM uf-set-c uf-set-d))
                  (ArrowM uf-set-a uf-set-a))
                #f))
(let ([uf-set-a (new-uf-set)])
  (check-exn #rx"occurs-check" (λ ()
    (unify uf-set-a
           (ArrowM uf-set-a uf-set-a)))))


;;;;;;;;;;;;;;;;
; type checker ;
;;;;;;;;;;;;;;;;

; typing rules for Macro-level phase 1 terms
;
; xM : tM ∈ Δ
; ------
; {Δ}; Γ ⊢ xM : tM
;
; {Δ, xM : in-tM}; Γ ⊢ bodyM : out-tM
; ------
; {Δ}; Γ ⊢ \xM. bodyM : in-tM -> out-tM
;
; {Δ}; Γ ⊢ funM : in-tM -> out-tM
; {Δ}; Γ ⊢ argM : in-tM
; ------
; {Δ}; Γ ⊢ funM argM : out-tM
;
; {Δ, funM : in-tM -> out-tM, xM : in-tM}; Γ ⊢ defM : out-tM
; {Δ, funM : in-tM -> out-tM}; Γ ⊢ bodyM : tM
; ------
; {Δ}; Γ ⊢ let-fun funM xM = defM in bodyM : tM
;
; ------
; {Δ}; Γ ⊢ zero : Nat
;
; ------
; {Δ}; Γ ⊢ succ : Nat -> Nat
;
; {Δ}; Γ ⊢ scrutM : Nat
; {Δ}; Γ ⊢ zero-branchM : tM
; {Δ, succ-xM : Nat}; Γ ⊢ succ-branchM : tM
; ------
; {Δ}; Γ ⊢ case-nat scrutM of
;            { zero -> zero-branchM
;            ; succ succ-xM -> succ-branchM
;            } : tM
;
; Δ; {Γ} ⊢ lowerU : inner-tZ
; ------
; {Δ}; Γ ⊢ 'lowerU : Dia inner-tZ
;
; {Δ}; Γ ⊢ defM : Dia lower-tZ
; {Δ}; Γ, xU : lower-tZ ⊢ bodyM : tM
; ------
; {Δ}; Γ ⊢ let-diaM xU = defM in bodyM : tM
(define (checkM delta gamma eeM ttM)
  (match eeM
    [(mk-varM xM)
     (unify ttM (hash-ref delta xM))]
    [(mk-λM xM bodyM)
     (define x-tM (new-uf-set))
     (define out-tM (new-uf-set))
     (and (checkM (hash-set delta xM x-tM) gamma
                  bodyM out-tM)
          (unify ttM (ArrowM x-tM out-tM)))]
    [(mk-appM funM argM)
     (define in-tM (new-uf-set))
     (define out-tM ttM)
     (and (checkM delta gamma funM (ArrowM in-tM out-tM))
          (checkM delta gamma argM in-tM)
          ttM)]
    [(mk-let-funM funM maybe-tM xM defM bodyM)
     (define in-tM (new-uf-set))
     (define out-tM (new-uf-set))
     (and (when maybe-tM
            (unify maybe-tM (ArrowM in-tM out-tM)))
          (checkM (hash-set* delta
                    funM (ArrowM in-tM out-tM)
                    xM in-tM)
                  gamma
                  defM out-tM)
          ; TODO: generalize
          (checkM (hash-set delta
                    funM (ArrowM in-tM out-tM))
                  gamma
                  bodyM ttM))]
    [(mk-zeroM)
     (unify ttM (NatM))]
    [(mk-succM)
     (unify ttM (ArrowM (NatM) (NatM)))]
    [(mk-case-natM scrutM zero-branchM succ-xM succ-branchM)
     (and (checkM delta gamma scrutM (NatM))
          (checkM delta gamma zero-branchM ttM)
          (checkM (hash-set delta succ-xM (NatM)) gamma
                  succ-branchM ttM))]
    [(mk-quoteM lowerU)
     (define lower-tZ (new-uf-set))
     (and (checkU delta gamma lowerU lower-tZ)
          (unify ttM (DiaM lower-tZ)))]
    [(mk-let-diaM xU maybe-tM defM bodyM)
     (define lower-tZ (new-uf-set))
     (and (when maybe-tM
            (unify maybe-tM (DiaM lower-tZ)))
          (checkM delta gamma defM (DiaM lower-tZ))
          (checkM delta (hash-set gamma xU lower-tZ) bodyM ttM))]))
(define (inferM eeM)
  (define ttM (new-uf-set))
  (and (checkM (hash) (hash) eeM ttM)
       (zonk ttM)))

; typing rules for Unexpanded phase 0 terms
;
; xU : tZ ∈ Δ
; ------
; Δ; {Γ} ⊢ xU : tZ
;
; Δ; {Γ, xU : in-tZ} ⊢ bodyU : out-tZ
; ------
; Δ; {Γ} ⊢ \xU. bodyU : in-tZ -> out-tZ
;
; Δ; {Γ} ⊢ funU : in-tZ -> out-tZ
; Δ; {Γ} ⊢ argU : in-tZ
; ------
; Δ; {Γ} ⊢ funU argU : out-tZ
;
; Δ; {Γ, funU : in-tZ -> out-tZ, xU : in-t0} ⊢ defU : out-tZ
; Δ; {Γ, funU : in-tZ -> out-tZ} ⊢ bodyU : tZ
; ------
; {Δ}; Γ ⊢ letfun funU xU = defU in bodyU : tZ
;
; ------
; Δ; {Γ} ⊢ zero : Nat
;
; ------
; Δ; {Γ} ⊢ succ : Nat -> Nat
;
; Δ; {Γ} ⊢ scrutU : Nat
; Δ; {Γ} ⊢ zero-branchU : tZ
; Δ; {Γ, succ-xU : Nat} ⊢ succ-branchU : tZ
; ------
; Δ; {Γ} ⊢ case-nat scrutU of
;            { zero -> zero-branchU
;            ; succ succ-xU -> succ-branchU
;            } : tZ
;
; {Δ}; Γ ⊢ higherM : Dia lower-tZ
; ------
; Δ; {Γ} ⊢ $higherM : lower-tZ
;
; {Δ}; Γ ⊢ defM : x-tM
; Δ, xM : x-tM; {Γ} ⊢ bodyU : tZ
; ------
; Δ; {Γ} ⊢ let-macroU xM = defM in bodyU : tZ
(define (checkU delta gamma eeU ttZ)
  (match eeU
    [(mk-varU xU)
     (unify ttZ (hash-ref gamma xU))]
    [(mk-λU xU bodyU)
     (define x-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (checkU delta (hash-set gamma xU x-tZ)
                  bodyU out-tZ)
          (unify ttZ (ArrowZ x-tZ out-tZ)))]
    [(mk-appU funU argU)
     (define in-tZ (new-uf-set))
     (define out-tZ ttZ)
     (and (checkU delta gamma funU (ArrowZ in-tZ out-tZ))
          (checkU delta gamma argU in-tZ)
          ttZ)]
    [(mk-let-funU funU maybe-tZ xU defU bodyU)
     (define in-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (when maybe-tZ
            (unify maybe-tZ (ArrowZ in-tZ out-tZ)))
          (checkU delta
                  (hash-set* gamma
                    funU (ArrowZ in-tZ out-tZ)
                    xU in-tZ)
                  defU out-tZ)
          ; TODO: generalize
          (checkU delta
                  (hash-set gamma
                    funU (ArrowZ in-tZ out-tZ))
                  bodyU ttZ))]
    [(mk-zeroU)
     (unify ttZ (NatZ))]
    [(mk-succU)
     (unify ttZ (ArrowZ (NatZ) (NatZ)))]
    [(mk-case-natU scrutU zero-branchU succ-xU succ-branchU)
     (and (checkU delta gamma scrutU (NatZ))
          (checkU delta gamma zero-branchU ttZ)
          (checkU delta (hash-set gamma succ-xU (NatZ))
                  succ-branchU ttZ))]
    [(mk-spliceU higherM)
     (and (checkM delta gamma higherM (DiaM ttZ))
          ttZ)]
    [(mk-let-macroU xM maybe-tM defM bodyU)
     (define def-tM (new-uf-set))
     (and (when maybe-tM
            (unify maybe-tM def-tM))
          (checkM delta gamma defM def-tM)
          (checkU (hash-set delta xM def-tM) gamma bodyU ttZ))]))
(define (inferU eeU)
  (define ttZ (new-uf-set))
  (and (checkU (hash) (hash) eeU ttZ)
       (zonk ttZ)))

; basic examples with inferM
(check-equal? (inferM (appM succM zeroM))
              (NatM))
(check-equal? (inferM (appM zeroM succM))
              #f)
(check-equal? (inferM (let-funM [(const-zero _) zeroM]
                        (appM const-zero succM)))
              (NatM))
(check-equal? (inferM (let-funM [(id x) x]
                        (appM id zeroM)))
              (NatM))
; TODO: uncomment once generalization is implemented
;(check-equal? (inferM (let-funM "id" "x" (varM "x")
;                        (appM
;                          (appM (varM "id") (varM "id"))
;                          (zeroM))))
;              (NatM))
(check-equal? (inferM (let-funM [(add x y)
                                 (case-natM x
                                   [zeroM
                                    y]
                                   [(succM x-1)
                                    (appM succM
                                      (appM add x-1 y))])]
                        (appM add (natM 2) (natM 2))))
              (NatM))
; same basic examples with inferU
(check-equal? (inferU (appU succU zeroU))
              (NatZ))
(check-equal? (inferU (appU zeroU succU))
              #f)
(check-equal? (inferU (let-funU [(const-zero _) zeroU]
                        (appU const-zero succU)))
              (NatZ))
(check-equal? (inferU (let-funU [(id x) x]
                        (appU id zeroU)))
              (NatZ))
; TODO: uncomment once generalization is implemented
;(check-equal? (inferU (let-funU "id" "x" (varU "x")
;                        (appU
;                          (appU (varU "id") (varU "id"))
;                          (zeroU))))
;              (NatZ))
(check-equal? (inferU (let-funU [(add x y)
                                 (case-natU x
                                   [zeroU
                                    y]
                                   [(succU x-1)
                                    (appU succU
                                      (appU add x-1 y))])]
                        (appU add (natU 2) (natU 2))))
              (NatZ))
; more interesting examples with let-diaM, quoteM, let-macroU, and spliceU:
(check-equal? (inferM (let-diaM [two (quoteM (natU 2))]
                        (quoteM (appU succU
                                  (appU succU
                                    two)))))
              (DiaM (NatZ)))
(check-equal? (inferU (let-funU [(add x y)
                                 (case-natU x
                                   [zeroU
                                    y]
                                   [(succU x-1)
                                    (appU succU
                                      (appU add x-1 y))])]
                        (let-funU [(mul x y)
                                   (case-natU x
                                     [zeroU
                                      zeroU]
                                     [(succU x-1)
                                      (appU add
                                        y
                                        (appU mul x-1 y))])]
                          (let-macroU [(power n diaX)
                                       (let-diaM [x diaX]
                                         (let-funM [(go n-1)
                                                    (case-natM n-1
                                                      [zeroM
                                                       (quoteM x)]
                                                      [(succM n-2)
                                                       (let-diaM [recur
                                                                  (appM go n-2)]
                                                         (quoteM
                                                           (appU mul x recur)))])]
                                           (case-natM n
                                             [zeroM
                                              (quoteM (natU 1))]
                                             [(succM n-1)
                                              (appM go n-1)])))]
                            (let-funU [(square x)
                                       (spliceU (appM power (natM 2) (quoteM x)))]
                              (appU square (appU square (natU 2))))))))
              (NatZ))

; typing rules for Expanded phase 0 terms
;
; xE : tZ ∈ Γ
; ------
; Γ ⊢ xE : tZ
;
; Γ, xE : in-tZ ⊢ bodyE : out-tZ
; ------
; Γ ⊢ \xE. bodyE : in-tZ -> out-tZ
;
; Γ ⊢ funE : in-tZ -> out-tZ
; Γ ⊢ argE : in-tZ
; ------
; Γ ⊢ funE argE : out-tZ
;
; Γ, funE : in-tZ -> out-tZ, xE : in-tZ ⊢ defE : out-tZ
; Γ, funE : in-tZ -> out-tZ ⊢ bodyE : tZ
; ------
; Γ ⊢ let-fun funE xE = defE in bodyE : tZ
;
; ------
; Γ ⊢ zeroE : Nat
;
; ------
; Γ ⊢ succE : Nat -> Nat
;
; Γ ⊢ scrutE : Nat
; Γ ⊢ zero-branchE : tZ
; Γ, succ-xE : Nat ⊢ succ-branchE : tZ
; ------
; Γ ⊢ case-natE scrutE of
;       { zero -> zero-branchE
;       ; succ succ-xE -> succ-branchE
;       } : tZ
(define (checkE gamma eeE ttZ)
  (match eeE
    [(mk-varE xE)
     (unify ttZ (hash-ref gamma xE))]
    [(mk-λE xE bodyE)
     (define x-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (checkE (hash-set gamma xE x-tZ)
                  bodyE out-tZ)
          (unify ttZ (ArrowZ x-tZ out-tZ)))]
    [(mk-appE funE argE)
     (define in-tZ (new-uf-set))
     (define out-tZ ttZ)
     (and (checkE gamma funE (ArrowZ in-tZ out-tZ))
          (checkE gamma argE in-tZ)
          ttZ)]
    [(mk-let-funE funE maybe-tZ xE defE bodyE)
     (define in-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (when maybe-tZ
            (unify maybe-tZ (ArrowZ in-tZ out-tZ)))
          (checkE (hash-set* gamma
                    funE (ArrowZ in-tZ out-tZ)
                    xE in-tZ)
                  defE out-tZ)
          ; TODO: generalize
          (checkE (hash-set gamma
                    funE (ArrowZ in-tZ out-tZ))
                  bodyE ttZ))]
    [(mk-zeroE)
     (unify ttZ (NatZ))]
    [(mk-succE)
     (unify ttZ (ArrowZ (NatZ) (NatZ)))]
    [(mk-case-natE scrutE zero-branchE succ-xE succ-branchE)
     (and (checkE gamma scrutE (NatZ))
          (checkE gamma zero-branchE ttZ)
          (checkE (hash-set gamma succ-xE (NatZ))
                  succ-branchE ttZ))]))
(define (inferE eeE)
  (define ttZ (new-uf-set))
  (and (checkE (hash) eeE ttZ)
       (zonk ttZ)))
; same basic examples with inferE
(check-equal? (inferE (appE succE zeroE))
              (NatZ))
(check-equal? (inferE (appE zeroE succE))
              #f)
(check-equal? (inferE (let-funE [(const-zero _) zeroE]
                        (appE const-zero succE)))
              (NatZ))
(check-equal? (inferE (let-funE [(id x) x]
                        (appE id zeroE)))
              (NatZ))
; TODO: uncomment once generalization is implemented
;(check-equal? (inferE (let-funE "id" "x" (varE "x")
;                        (appE
;                          (appE (varE "id") (varE "id"))
;                          (zeroE))))
;              (NatZ))
(check-equal? (inferE (let-funE [(add x y)
                                 (case-natE x
                                   [zeroE
                                    y]
                                   [(succE x-1)
                                    (appE succE
                                      (appE add x-1 y))])]
                        (appE add (natE 2) (natE 2))))
              (NatZ))


;;;;;;;;;;;;;;;
; interpreter ;
;;;;;;;;;;;;;;;

; big-steps semantics for Macro-level phase 1 terms. note that
;
;   Δ; {Γ̅} ⊢ eU => eE
;
; is expansion, not evaluation, and that Γ̅ maps variables to Expanded phase 0
; terms, not to phase 0 values.
;
; xM ↦ vM ∈ Δ
; ------
; {Δ}; Γ̅ ⊢ xM => vM
;
; ------
; {Δ}; Γ̅ ⊢ \xM. bodyM => clo Δ Γ̅ xM bodyM
;
; {Δ}; Γ̅ ⊢ funM => clo clo-Δ clo-Γ xM bodyM
; {Δ}; Γ̅ ⊢ argM => inM
; {clo-Δ, xM ↦ inM}; clo-Γ ⊢ bodyM => outM
; ------
; {Δ}; Γ̅ ⊢ funM arg2M => outM
;
; ext-Δ@{Δ, funM ↦ clo ext-Δ Γ̅ xM defM}; Γ̅ ⊢ bodyM => vM
; ------
; {Δ}; Γ̅ ⊢ let-fun funM xM = defM in bodyM => vM
;
; ------
; {Δ}; Γ̅ ⊢ zero => zero
;
; ------
; {Δ}; Γ̅ ⊢ succ => succ
;
; {Δ}; Γ̅ ⊢ funM => succ
; {Δ}; Γ̅ ⊢ argM => nM
; ------
; {Δ}; Γ̅ ⊢ funM arg2M => succ nM
;
; {Δ}; Γ̅ ⊢ scrutM => zero
; {Δ}; Γ̅ ⊢ zero-branchM => vM
; ------
; {Δ}; Γ̅ ⊢ case-nat scrutM of
;            { zero -> zero-branchM
;            ; succ succ-xM -> succ-branchM
;            }
;       => vM
;
; {Δ}; Γ̅ ⊢ scrutM => succ nM
; {Δ, succ-xM ↦ nM}; Γ̅ ⊢ succ-branchM => vM
; ------
; {Δ}; Γ̅ ⊢ case-nat scrutM of
;            { zero -> zero-branchM
;            ; succ succ-xM -> succ-branchM
;            }
;       => vM
;
; Δ; {Γ̅} ⊢ lowerU => lowerE
; ------
; {Δ}; Γ̅ ⊢ 'lowerU => 'lowerE
;
; {Δ}; Γ̅ ⊢ defM => 'lowerE
; {Δ}; Γ, xU ↦ lowerE ⊢ bodyM => vM
; ------
; {Δ}; Γ̅̅ ⊢ let-diaM xU = defM in body
(struct clo-valM (delta gamma-bar xM bodyM) #:transparent)
(struct succ-valM () #:transparent)
(struct nat-valM (n) #:transparent)
(struct quoted-valM (exprE) #:transparent)
(define (evalM delta gamma-bar eeM)
  (match eeM
    [(mk-varM xM)
     ((hash-ref delta xM))]
    [(mk-λM xM bodyM)
     (clo-valM delta gamma-bar xM bodyM)]
    [(mk-appM funM argM)
     (match (evalM delta gamma-bar funM)
       [(clo-valM clo-delta clo-gamma-bar xM bodyM)
        (define inM (evalM delta gamma-bar argM))
        (evalM (hash-set clo-delta xM (λ () inM)) clo-gamma-bar bodyM)]
       [(succ-valM)
        (match (evalM delta gamma-bar argM)
          [(nat-valM inM)
           (nat-valM (+ inM 1))])])]
    [(mk-let-funM funM _maybe-tM xM defM bodyM)
     (define (mk-fun)
       (clo-valM (hash-set delta funM mk-fun) gamma-bar xM defM))
     (evalM (hash-set delta funM mk-fun) gamma-bar bodyM)]
    [(mk-zeroM)
     (nat-valM 0)]
    [(mk-succM)
     (succ-valM)]
    [(mk-case-natM scrutM zero-branchM succ-xM succ-branchM)
     (match (evalM delta gamma-bar scrutM)
       [(nat-valM 0)
        (evalM delta gamma-bar zero-branchM)]
       [(nat-valM n)
        (define x (nat-valM (- n 1)))
        (evalM (hash-set delta succ-xM (λ () x)) gamma-bar succ-branchM)])]
    [(mk-quoteM lowerU)
     (quoted-valM (expandU delta gamma-bar lowerU))]
    [(mk-let-diaM xU _maybe-tM defM bodyM)
     (match (evalM delta gamma-bar defM)
       [(quoted-valM lowerE)
        (evalM delta (hash-set gamma-bar xU lowerE) bodyM)])]))
(define (eval-closedM eeM)
  (evalM (hash) (hash) eeM))

; big-steps semantics for expanding Unexpanded phase 0 terms
;
; xU ↦ eE ∈ Γ̅̅
; ------
; Δ; {Γ̅} ⊢ xU => eE
;
; Δ; {Γ̅, xU ↦ xE} ⊢ bodyU => bodyE
; ------
; Δ; {Γ̅} ⊢ \xU. bodyU => \xE. bodyE
;
; Δ; {Γ̅} ⊢ funU => funE
; Δ; {Γ̅} ⊢ argU => argE
; ------
; Δ; {Γ̅} ⊢ funU argU => funE argE
;
; Δ; {Γ̅, funU ↦ funE, xU ↦ xE} ⊢ defU => defE
; Δ; {Γ̅, funU ↦ funE} ⊢ bodyU => bodyE
; ------
; Δ; {Γ̅} ⊢ let-fun funU xU = defU in bodyU
;       => let-fun funE xE = defE in bodyE
;
; ------
; Δ; {Γ̅} ⊢ zeroU => zeroE
;
; ------
; Δ; {Γ̅} ⊢ succU => succE
;
; Δ; {Γ̅} ⊢ scrutU => scrutE
; Δ; {Γ̅} ⊢ zero-branchU => zero-branchE
; Δ; {Γ̅, succ-xU ↦ succ-xE} ⊢ succ-branchU => succ-branchE
; ------
; Δ; {Γ̅} ⊢ case-natU scrutU of
;            { zero -> zero-branchU
;            ; succ succ-xU -> succ-branchU
;            }
;       => case-natE scrutE of
;           { zero -> zero-branchE
;           ; succ succ-xE -> succ-branchE
;           }
;
; {Δ}; Γ̅ ⊢ higherM => 'lowerE
; ------
; Δ; {Γ̅} ⊢ $higherM => lowerE
;
; {Δ}; Γ̅ ⊢ defM => vM
; Δ, xU ↦ vM; {Γ̅} ⊢ bodyU => bodyE
; ------
; Δ; {Γ̅} ⊢ let-macroM xU = defM in bodyU => bodyE
(define (expandU delta gamma-bar eeU)
  (match eeU
    [(mk-varU xU)
     (hash-ref gamma-bar xU)]
    [(mk-λU xU bodyU)
     (define bodyE (expandU delta (hash-set gamma-bar
                                    xU (mk-varE xU))
                            bodyU))
     (mk-λE xU bodyE)]
    [(mk-appU funU argU)
     (define funE (expandU delta gamma-bar funU))
     (define argE (expandU delta gamma-bar argU))
     (mk-appE funE argE)]
    [(mk-let-funU funU maybe-tZ xU defU bodyU)
     (define defE (expandU delta (hash-set* gamma-bar
                                   funU (mk-varE funU)
                                   xU (mk-varE xU))
                           defU))
     (define bodyE (expandU delta (hash-set gamma-bar
                                    funU (mk-varE funU))
                            bodyU))
     (mk-let-funE funU maybe-tZ xU defE bodyE)]
    [(mk-zeroU)
     (mk-zeroE)]
    [(mk-succU)
     (mk-succE)]
    [(mk-case-natU scrutU zero-branchU succ-xU succ-branchU)
     (define scrutE (expandU delta gamma-bar scrutU))
     (define zero-branchE (expandU delta gamma-bar zero-branchU))
     (define succ-branchE (expandU delta (hash-set gamma-bar
                                           succ-xU (mk-varE succ-xU))
                                   succ-branchU))
     (mk-case-natE scrutE zero-branchE succ-xU succ-branchE)]
    [(mk-spliceU higherM)
     (match (evalM delta gamma-bar higherM)
       [(quoted-valM lowerE)
        lowerE])]
    [(mk-let-macroU xU _maybe-tM defM bodyU)
     (define vM (evalM delta gamma-bar defM))
     (expandU (hash-set delta xU (λ () vM)) gamma-bar
              bodyU)]))
(define (expand-closedU eeU)
  (expandU (hash) (hash) eeU))
; the usual basic examples, with evalM
(check-equal? (eval-closedM (appM succM zeroM))
              (nat-valM 1))
; TODO: throw and catch runtime errors
;(check-equal? (eval-closedM (appM zeroM succM))
;              #f)
(check-equal? (eval-closedM (let-funM [(const-zero _) zeroM]
                              (appM const-zero succM)))
              (nat-valM 0))
(check-equal? (eval-closedM (let-funM [(id x) x]
                              (appM id zeroM)))
              (nat-valM 0))
(check-equal? (eval-closedM (let-funM [(id x) x]
                              (appM id id zeroM)))
              (nat-valM 0))
(check-equal? (eval-closedM (let-funM [(add x y)
                                       (case-natM x
                                         [zeroM
                                          y]
                                         [(succM x-1)
                                          (appM succM
                                            (appM add x-1 y))])]
                              (appM add (natM 2) (natM 2))))
              (nat-valM 4))
;; more interesting examples with let-diaM, quoteM, let-macroU, and spliceU:
(check-equal? (eval-closedM (let-diaM [two (quoteM (natU 2))]
                              (quoteM (appU succU
                                        (appU succU
                                          two)))))
              (quoted-valM (natE 4)))
(check-equal? (expand-closedU (let-funU [(add x y)
                                         (case-natU x
                                           [zeroU
                                            y]
                                           [(succU x-1)
                                            (appU succU
                                              (appU add x-1 y))])]
                                (let-funU [(mul x y)
                                           (case-natU x
                                             [zeroU
                                              zeroU]
                                             [(succU x-1)
                                              (appU add
                                                y
                                                (appU mul x-1 y))])]
                                  (let-macroU [(power n diaX)
                                               (let-diaM [x diaX]
                                                 (let-funM [(go n-1)
                                                            (case-natM n-1
                                                              [zeroM
                                                               (quoteM x)]
                                                              [(succM n-2)
                                                               (let-diaM [recur
                                                                          (appM go n-2)]
                                                                 (quoteM
                                                                   (appU mul x recur)))])]
                                                   (case-natM n
                                                     [zeroM
                                                      (quoteM (natU 1))]
                                                     [(succM n-1)
                                                      (appM go n-1)])))]
                                    (let-funU [(square x)
                                               (spliceU (appM power
                                                              (natM 2)
                                                              (quoteM x)))]
                                      (appU square (appU square (natU 2))))))))
              (let-funE [(add x) (λE (y)
                                   (case-natE x
                                     [zeroE
                                      y]
                                     [(succE x-1)
                                      (appE succE
                                        (appE add x-1 y))]))]
                (let-funE [(mul x) (λE (y)
                                     (case-natE x
                                       [zeroE
                                        zeroE]
                                       [(succE x-1)
                                        (appE add
                                          y
                                          (appE mul x-1 y))]))]
                  (let-funE [(square x)
                             (appE mul x x)]
                    (appE square
                      (appE square
                        (natE 2)))))))

; big steps semantics for Expanded phase 0 terms
;
; xE ↦ vE ∈ Γ
; ------
; Γ ⊢ xE => vE
;
; ------
; Γ ⊢ \xE. bodyE => clo Γ xE bodyE
;
; Γ ⊢ funE => clo clo-Γ xE defE
; Γ ⊢ argE => inE
; clo-Γ, xE ↦ inE ⊢ bodyE => outE
; ------
; Γ ⊢ funE argE => outE
;
; ext-Γ@(Γ, funE ↦ clo ext-Γ xE defE); Γ ⊢ bodyE => vE
; ------
; Γ ⊢ let-fun funE xE = defE in bodyE => vE
;
; ------
; Γ ⊢ zeroE => zero
;
; ------
; Γ ⊢ succE => succ
;
; Γ ⊢ funE => succ
; Γ ⊢ argE => nE
; ------
; Γ ⊢ funE argE => succ nE
;
; Γ ⊢ scrutE => zero
; Γ ⊢ zero-branchE => vE
; ------
; Γ ⊢ case-nat scrutE of
;       { zero -> zero-branchE
;       ; succ succ-xE -> succ-branchE
;       }
;     => vE
;
; Γ ⊢ scrutE => succ nE
; Γ, succ-xE ↦ nE ⊢ succ-branchE => vE
; ------
; Γ ⊢ case-nat scrutE of
;       { zero -> zero-branchE
;       ; succ succ-xE -> succ-branchE
;       }
;  => vE
(struct clo-valE (gamma xE bodyE) #:transparent)
(struct succ-valE () #:transparent)
(struct nat-valE (nE) #:transparent)
(define (evalE gamma eeE)
  (match eeE
    [(mk-varE xE)
     ((hash-ref gamma xE))]
    [(mk-λE xE bodyE)
     (clo-valE gamma xE bodyE)]
    [(mk-appE funE argE)
     (match (evalE gamma funE)
       [(clo-valE clo-gamma xE bodyE)
        (define inE (evalE gamma argE))
        (evalE (hash-set clo-gamma xE (λ () inE)) bodyE)]
       [(succ-valE)
        (match (evalE gamma argE)
          [(nat-valE nE)
           (nat-valE (+ nE 1))])])]
    [(mk-let-funE funE _maybe-tZ xE defE bodyE)
     (define (mk-fun)
       (clo-valE (hash-set gamma funE mk-fun) xE defE))
     (evalE (hash-set gamma funE mk-fun) bodyE)]
    [(mk-zeroE)
     (nat-valE 0)]
    [(mk-succE)
     (succ-valE)]
    [(mk-case-natE scrutE zero-branchE succ-xE succ-branchE)
     (match (evalE gamma scrutE)
       [(nat-valE 0)
        (evalE gamma zero-branchE)]
       [(nat-valE nE)
        (define x (nat-valE (- nE 1)))
        (evalE (hash-set gamma succ-xE (λ () x)) succ-branchE)])]))
(define (eval-closedE eeE)
  (evalE (hash) eeE))
; the usual basic examples, with evalE
(check-equal? (eval-closedE (appE succE zeroE))
              (nat-valE 1))
; TODO: throw and catch runtime errors
;(check-equal? (eval-closedE (appE zeroE succE))
;              #f)
(check-equal? (eval-closedE (let-funE [(const-zero _) zeroE]
                              (appE const-zero succE)))
              (nat-valE 0))
(check-equal? (eval-closedE (let-funE [(id x) x]
                              (appE id zeroE)))
              (nat-valE 0))
(check-equal? (eval-closedE (let-funE [(id x) x]
                              (appE id id zeroE)))
              (nat-valE 0))
(check-equal? (eval-closedE (let-funE [(add x y)
                                       (case-natE x
                                         [zeroE
                                          y]
                                         [(succE x-1)
                                          (appE succE
                                            (appE add x-1 y))])]
                              (appE add (natE 2) (natE 2))))
              (nat-valE 4))
