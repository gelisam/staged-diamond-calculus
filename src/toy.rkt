#lang racket
(require rackunit)
(require data/union-find)

(define-syntax (and-let* stx)
  (syntax-case stx ()
    [(_ () body ...)
     #`(begin body ...)]
    [(_ ([x1 e1] [x2 v2] ...) body ...)
     #`(let ([x1 e1])
         (and x1
              (and-let* ([x2 v2] ...) body ...)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; phase 1 (*M*acro-level) terms with phase 0 terms inside of them
; eM ::= xM | \xM. eM | eM eM
;      | zero | succ | case-nat eM of {zero -> eM; succ xM -> eM}
;      | 'eU | let-diaM xU = eM in eM
(struct varM (xM) #:transparent)
(struct λM (xM bodyM) #:transparent)
(struct appM (funM argM) #:transparent)
(struct let-funM (funM xM defM bodyM) #:transparent)
(struct zeroM () #:transparent)
(struct succM () #:transparent)
(struct case-natM (scrutM zero-branchM succ-xM succ-branchM) #:transparent)
(struct quoteM (lowerU) #:transparent)
(struct let-diaM (xU defM bodyM) #:transparent)

; *U*nexpanded phase 0 terms with phase 1 terms inside of them
; eU ::= xU | \xU. eU | eU eU
;      | zero | succ | case-nat eM of {zero -> eM; succ xU -> eM}
;      | $eM | let-macroU xM = eM in eU
(struct varU (xU) #:transparent)
(struct λU (xU bodyU) #:transparent)
(struct appU (funU argU) #:transparent)
(struct let-funU (funU xU defU bodyU) #:transparent)
(struct zeroU () #:transparent)
(struct succU () #:transparent)
(struct case-natU (scrutU zero-branchU succ-xU succ-branchU) #:transparent)
(struct spliceU (termM) #:transparent)
(struct let-macroU (xM defM bodyU) #:transparent)

; *E*xpanded phase 0 terms, with no phase 1 terms
; eE ::= xE | \xE. eE | eE eE
;      | zero | succ | case-nat eE of {zero -> eE; succ x -> eE}
(struct varE (xE) #:transparent)
(struct λE (xE bodyE) #:transparent)
(struct appE (funE argE) #:transparent)
(struct let-funE (funE xE defE bodyE) #:transparent)
(struct zeroE () #:transparent)
(struct succE () #:transparent)
(struct case-natE (scrutE zero-branchE succ-xE succ-branchE) #:transparent)


; phase 1 (*M*acro-level) types with phase 0 types inside of them
; tM ::= tM -> tM | NatM | Dia tZ
(struct ArrowM (in-tM out-tM) #:transparent)
(struct NatM () #:transparent)
(struct DiaM (lower-tZ) #:transparent)

; phase 0 (*Z*ero) types with no phase 1 types
; tZ ::= tZ -> tZ | NatZ
(struct ArrowZ (in-tZ out-tZ) #:transparent)
(struct NatZ () #:transparent)


; unification

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
    [(varM xM)
     (unify ttM (hash-ref delta xM))]
    [(λM xM bodyM)
     (define x-tM (new-uf-set))
     (define out-tM (new-uf-set))
     (and (checkM (hash-set delta xM x-tM) gamma
                  bodyM out-tM)
          (unify ttM (ArrowM x-tM out-tM)))]
    [(appM funM argM)
     (define in-tM (new-uf-set))
     (define out-tM ttM)
     (and (checkM delta gamma funM (ArrowM in-tM out-tM))
          (checkM delta gamma argM in-tM)
          ttM)]
    [(let-funM funM xM defM bodyM)
     (define in-tM (new-uf-set))
     (define out-tM (new-uf-set))
     (and (checkM (hash-set* delta
                    funM (ArrowM in-tM out-tM)
                    xM in-tM)
                  gamma
                  defM out-tM)
          ; TODO: generalize
          (checkM (hash-set delta
                    funM (ArrowM in-tM out-tM))
                  gamma
                  bodyM ttM))]
    [(zeroM)
     (unify ttM (NatM))]
    [(succM)
     (unify ttM (ArrowM (NatM) (NatM)))]
    [(case-natM scrutM zero-branchM succ-xM succ-branchM)
     (and (checkM delta gamma scrutM (NatM))
          (checkM delta gamma zero-branchM ttM)
          (checkM (hash-set delta succ-xM (NatM)) gamma
                  succ-branchM ttM))]
    [(quoteM lowerU)
     (define lower-tZ (new-uf-set))
     (and (checkU delta gamma lowerU lower-tZ)
          (unify ttM (DiaM lower-tZ)))]
    [(let-diaM xU defM bodyM)
     (define lower-tZ (new-uf-set))
     (and (checkM delta gamma defM (DiaM lower-tZ))
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
    [(varU xU)
     (unify ttZ (hash-ref gamma xU))]
    [(λU xU bodyU)
     (define x-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (checkU delta (hash-set gamma xU x-tZ)
                  bodyU out-tZ)
          (unify ttZ (ArrowZ x-tZ out-tZ)))]
    [(appU funU argU)
     (define in-tZ (new-uf-set))
     (define out-tZ ttZ)
     (and (checkU delta gamma funU (ArrowZ in-tZ out-tZ))
          (checkU delta gamma argU in-tZ)
          ttZ)]
    [(let-funU funU xU defU bodyU)
     (define in-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (checkU delta
                  (hash-set* gamma
                    funU (ArrowZ in-tZ out-tZ)
                    xU in-tZ)
                  defU out-tZ)
          ; TODO: generalize
          (checkU delta
                  (hash-set gamma
                    funU (ArrowZ in-tZ out-tZ))
                  bodyU ttZ))]
    [(zeroU)
     (unify ttZ (NatZ))]
    [(succU)
     (unify ttZ (ArrowZ (NatZ) (NatZ)))]
    [(case-natU scrutU zero-branchU succ-xU succ-branchU)
     (and (checkU delta gamma scrutU (NatZ))
          (checkU delta gamma zero-branchU ttZ)
          (checkU delta (hash-set gamma succ-xU (NatZ))
                  succ-branchU ttZ))]
    [(spliceU higherM)
     (and (checkM delta gamma higherM (DiaM ttZ))
          ttZ)]
    [(let-macroU xM defM bodyU)
     (define def-tM (new-uf-set))
     (and (checkM delta gamma defM def-tM)
          (checkU (hash-set delta xM def-tM) gamma bodyU ttZ))]))
(define (inferU eeU)
  (define ttZ (new-uf-set))
  (and (checkU (hash) (hash) eeU ttZ)
       (zonk ttZ)))

; basic examples with inferM
(check-equal? (inferM (appM (succM) (zeroM)))
              (NatM))
(check-equal? (inferM (appM (zeroM) (succM)))
              #f)
(check-equal? (inferM (let-funM "const-zero" "_" (zeroM)
                        (appM (varM "const-zero") (succM))))
              (NatM))
(check-equal? (inferM (let-funM "id" "x" (varM "x")
                        (appM (varM "id") (zeroM))))
              (NatM))
; TODO: uncomment once generalization is implemented
;(check-equal? (inferM (let-funM "id" "x" (varM "x")
;                        (appM
;                          (appM (varM "id") (varM "id"))
;                          (zeroM))))
;              (NatM))
(check-equal? (inferM (let-funM "add" "x" (λM "y"
                                            (case-natM (varM "x")
                                              (varM "y")
                                              "x-1" (appM
                                                      (appM (varM "add")
                                                        (varM "x-1"))
                                                      (varM "y"))))
                        (appM
                          (appM (varM "add")
                            (appM (succM) (appM (succM) (zeroM))))
                          (appM (succM) (appM (succM) (zeroM))))))
              (NatM))
; same basic examples with inferU
(check-equal? (inferU (appU (succU) (zeroU)))
              (NatZ))
(check-equal? (inferU (appU (zeroU) (succU)))
              #f)
(check-equal? (inferU (let-funU "const-zero" "_" (zeroU)
                        (appU (varU "const-zero") (succU))))
              (NatZ))
(check-equal? (inferU (let-funU "id" "x" (varU "x")
                        (appU (varU "id") (zeroU))))
              (NatZ))
; TODO: uncomment once generalization is implemented
;(check-equal? (inferU (let-funU "id" "x" (varU "x")
;                        (appU
;                          (appU (varU "id") (varU "id"))
;                          (zeroU))))
;              (NatZ))
(check-equal? (inferU (let-funU "add" "x" (λU "y"
                                            (case-natU (varU "x")
                                              (varU "y")
                                              "x-1" (appU
                                                      (appU (varU "add")
                                                        (varU "x-1"))
                                                      (varU "y"))))
                        (appU
                          (appU (varU "add")
                            (appU (succU) (appU (succU) (zeroU))))
                          (appU (succU) (appU (succU) (zeroU))))))
              (NatZ))
; more interesting examples with let-diaM, quoteM, let-macroU, and spliceU:
(check-equal? (inferM (let-diaM "two" (quoteM (appU (succU)
                                                (appU (succU)
                                                  (zeroU))))
                        (quoteM (appU (succU)
                                  (appU (succU)
                                    (varU "two"))))))
              (DiaM (NatZ)))
(check-equal? (inferU (let-funU "add" "x" (λU "y"
                                            (case-natU (varU "x")
                                              (varU "y")
                                              "x-1" (appU
                                                      (appU (varU "add")
                                                        (varU "x-1"))
                                                      (varU "y"))))
                        (let-funU "mul" "x" (λU "y"
                                              (case-natU (varU "x")
                                                (zeroU)
                                                "x-1" (appU
                                                        (appU (varU "add")
                                                          (varU "y"))
                                                        (appU
                                                          (appU (varU "mul")
                                                            (varU "x-1"))
                                                          (varU "y")))))
                          (let-macroU "power" (λM "n"
                                                (quoteM (λU "x"
                                                  (spliceU
                                                    (let-funM "go" "n-1"
                                                                   (case-natM (varM "n-1")
                                                                     (quoteM (varU "x"))
                                                                     "n-2" (let-diaM "recur"
                                                                                     (appM (varM "go")
                                                                                           (varM "n-2"))
                                                                             (quoteM
                                                                               (appU
                                                                                 (appU (varU "mul")
                                                                                   (varU "x"))
                                                                                 (varU "recur")))))
                                                      (case-natM (varM "n")
                                                        (quoteM (appU (succU) (zeroU)))
                                                        "n-1" (appM (varM "go") (varM "n-1"))))))))
                            (let-funU "double" "x" (appU
                                                     (spliceU (appM (varM "power")
                                                                (appM (succM)
                                                                  (appM (succM)
                                                                    (zeroM)))))
                                                     (varU "x"))
                              (appU (varU "double")
                                (appU (varU "double")
                                  (appU (varU "double")
                                    (appU (succU) (zeroU))))))))))
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
    [(varE xE)
     (unify ttZ (hash-ref gamma xE))]
    [(λE xE bodyE)
     (define x-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (checkE (hash-set gamma xE x-tZ)
                  bodyE out-tZ)
          (unify ttZ (ArrowZ x-tZ out-tZ)))]
    [(appE funE argE)
     (define in-tZ (new-uf-set))
     (define out-tZ ttZ)
     (and (checkE gamma funE (ArrowZ in-tZ out-tZ))
          (checkE gamma argE in-tZ)
          ttZ)]
    [(let-funE funE xE defE bodyE)
     (define in-tZ (new-uf-set))
     (define out-tZ (new-uf-set))
     (and (checkE (hash-set* gamma
                    funE (ArrowZ in-tZ out-tZ)
                    xE in-tZ)
                  defE out-tZ)
          ; TODO: generalize
          (checkE (hash-set gamma
                    funE (ArrowZ in-tZ out-tZ))
                  bodyE ttZ))]
    [(zeroE)
     (unify ttZ (NatZ))]
    [(succE)
     (unify ttZ (ArrowZ (NatZ) (NatZ)))]
    [(case-natE scrutE zero-branchE succ-xE succ-branchE)
     (and (checkE gamma scrutE (NatZ))
          (checkE gamma zero-branchE ttZ)
          (checkE (hash-set gamma succ-xE (NatZ))
                  succ-branchE ttZ))]))
(define (inferE eeE)
  (define ttZ (new-uf-set))
  (and (checkE (hash) eeE ttZ)
       (zonk ttZ)))
; same basic examples with inferE
(check-equal? (inferE (appE (succE) (zeroE)))
              (NatZ))
(check-equal? (inferE (appE (zeroE) (succE)))
              #f)
(check-equal? (inferE (let-funE "const-zero" "_" (zeroE)
                        (appE (varE "const-zero") (succE))))
              (NatZ))
(check-equal? (inferE (let-funE "id" "x" (varE "x")
                        (appE (varE "id") (zeroE))))
              (NatZ))
; TODO: uncomment once generalization is implemented
;(check-equal? (inferE (let-funE "id" "x" (varE "x")
;                        (appE
;                          (appE (varE "id") (varE "id"))
;                          (zeroE))))
;              (NatZ))
(check-equal? (inferE (let-funE "add" "x" (λE "y"
                                            (case-natE (varE "x")
                                              (varE "y")
                                              "x-1" (appE
                                                      (appE (varE "add")
                                                        (varE "x-1"))
                                                      (varE "y"))))
                        (appE
                          (appE (varE "add")
                            (appE (succE) (appE (succE) (zeroE))))
                          (appE (succE) (appE (succE) (zeroE))))))
              (NatZ))