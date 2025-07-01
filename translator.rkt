#lang racket
(provide to-ocaml to-mk)

(define (extend-env var ty env)
  `((,var . (Val . ,ty)) . ,env))

(define (extend-env* vars tys env)
  (append (map (λ (v t) (cons v `(Val . ,t))) vars tys) env))

(define (collect-names prgm)
  (match prgm
    (`() `())
    (`((defrel (,name (,vs : ,tys) ...) ,g ,gs ...) . ,defs)
     `((,name . (Rel . ,tys)) . ,(collect-names defs)))
    (`((run ,n ((,vs : ,tys) ...) ,g ,gs ...) . ,defs)
     (collect-names defs))))

(define (all-rels env)
  (map car
    (filter (λ (p)
              (match p
                (`(,var . (Rel . ,_)) #t)
                (_ #f)))
            env)))

(define (var-type var env)
  (match env
    (`() (error 'var-type "Value ~a not found" var))
    (`((,var^ . (Val . ,t)) . ,env^) #:when (eqv? var^ var) t)
    (`((,_ . ,_) . ,env^) (var-type var env^))))

(define (rel-type var env)
  (match env
    (`() (error 'rel-type "Relation ~a not found" var))
    (`((,var^ . (Rel . ,tys)) . ,env^) #:when (eqv? var^ var) tys)
    (`((,_ . ,_) . ,env^) (rel-type var env^))))

(define (var-index-type v env)
  (match env
    (`() (error 'trans-val "Not found: ~a" v))
    (`((,var . (Val . ,t)) . ,env^)
     #:when (eqv? var v)
     `(0 . ,t))
    (`((,var . ,_) . ,env^)
     (match (var-index-type v env^)
       (`(,n . ,t) `(,(add1 n) . ,t))))))

;;; Language 1
;;; A relation definition
;;; Rel := (defrel (Symbol (Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A goal
;;; Goal := (Symbol v₁ ...)
;;;      |  (conj Goal ...)
;;;      |  (disj Goal ...)
;;;      |  (== vτ v₁ v₂)
;;;      |  (=/= vτ v₁ v₂)
;;;      |  (fresh ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A value
;;; v := Symbol
;;;   |  Number
;;;   |  (v . v)
;;;   |  ()
;;;   |  (quote v)
;;;   |  (quasiquote v)
;;;   |  (unquote Symbol)
;;;
;;; A value type
;;; vτ  := Unit
;;;     |  (Pair vτ₁ vτ₂)
;;;     |  (Sum vτ₁ vτ₂)
;;;
;;; A query
;;; Query := (run n ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A program
;;; Prgm = Rel ... Query

;;; Pass 1: simplify values in a goal
(define (eval-val v)
  (match v
    (`,v #:when (symbol? v) v)
    (`,n #:when (natural? n) n)
    (`(quote ,v^) (eval-quote v^))
    (`(quasiquote ,v^) (eval-quasiquote v^))
    (`(list ,vs ...)
     (map eval-val vs))
    (`(,a . ,d)
     (cons (eval-val a) (eval-val d)))
    (`() '())
    (_ (error 'eval-val "Unsupported expression: ~a" v))))

(define (eval-quote v)
  (match v
    (`,s
     #:when (symbol? s)
     (error 'eval-quote "Atoms are not supported in this miniKanren, given ~a!" s))
    (`,n #:when (natural? n) n)
    (`() '())
    (`(,a . ,d)
     (cons (eval-quote a) (eval-quote d)))
    (_ (error 'eval-quote "Unsupported expression: ~a" v))))

(define (eval-quasiquote v)
  (match v
    (`,s
     #:when (symbol? s)
     (error 'eval-quasiquote "Atoms are not supported in this miniKanren, given ~a!" s))
    (`,n #:when (natural? n) n)
    (`(,f ,a) #:when (and (eqv? f 'unquote) (symbol? a)) a)
    (`() '())
    (`(,a . ,d)
     (cons (eval-quasiquote a) (eval-quasiquote d)))
    (_ (error 'eval-quasiquote "Unsupported expression: ~a" v))))

(define (eval-goal g env)
  (match g
    (`(conj ,g ,gs ...)
     `(conj ,@(map (λ (g) (eval-goal g env)) `(,g . ,gs))))
    (`(disj ,g ,gs ...)
     `(disj ,@(map (λ (g) (eval-goal g env)) `(,g . ,gs))))
    (`(== ,ty ,v1 ,v2)
     `(== ,ty ,(eval-val v1) ,(eval-val v2)))
    (`(=/= ,ty ,v1 ,v2)
     `(=/= ,ty ,(eval-val v1) ,(eval-val v2)))
    (`(fresh ((,vs : ,tys) ...) ,g ,gs ...)
     `(fresh (,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,@(map (λ (g) (eval-goal g env)) `(,g . ,gs))))
    (`(,R ,vs ...) #:when (symbol? R)
     `(,R ,@(map (λ (v) (eval-val v)) vs)))))

(define (eval-def def env)
  (match def
    (`(defrel (,rel (,vs : ,tys) ...) ,g ,gs ...)
     #:when (symbol? rel)
     `(defrel (,rel ,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,@(map (λ (g) (eval-goal g (extend-env* vs tys env)))
            `(,g . ,gs))))
    (`(run ,n ((,vs : ,tys) ...) ,g ,gs ...)
     `(run ,n (,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,@(map (λ (g) (eval-goal g (extend-env* vs tys env)))
            `(,g . ,gs))))))

;;; Language 2
;;; A relation definition
;;; Rel := (defrel (Symbol (Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A goal
;;; Goal := (Symbol v₁ ...)
;;;      |  (conj Goal ...)
;;;      |  (disj Goal ...)
;;;      |  (== vτ v₁ v₂)
;;;      |  (=/= vτ v₁ v₂)
;;;      |  (fresh ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A value
;;; v := Symbol
;;;   |  Number
;;;   |  (val . val)
;;;   |  ()
;;;
;;; A value type
;;; vτ  := Unit
;;;     |  (Pair vτ₁ vτ₂)
;;;     |  (Sum vτ₁ vτ₂)
;;;
;;; A query
;;; Query := (run n ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A program
;;; Prgm = Rel ... Query

;;; Pass 2: simplify arguments of a goal
(define (simp-val val ty k)
  (match* (val ty)
    ((`() `Unit)
     (let ((var (gensym)))
       `(fresh ((,var : Unit))
          (conj (soleo ,var) ,(k var)))))
    ((`,var _) #:when (symbol? var) (k var))
    ((0 `Unit)
     (let ((var (gensym)))
       `(fresh ((,var : Unit))
          (conj (soleo ,var) ,(k var)))))
    ((0 `(Sum Unit ,ty^))
     (let ((var1 (gensym))
           (var2 (gensym)))
       `(fresh ((,var1 : ,ty) (,var2 : Unit))
          (conj (lefto ,var1 ,var2) ,(k var1)))))
    ((`,n `(Sum Unit ,ty^))
     #:when (natural? n)
     (simp-val (sub1 n) ty^
       (λ (var2)
         (let ((var1 (gensym)))
           `(fresh ((,var1 : ,ty))
              (conj (righto ,var1 ,var2)
                    ,(k var1)))))))
    ((`(,a . ,d) `(Pair ,ty1 ,ty2))
     (simp-val a ty1
       (λ (var1)
         (simp-val d ty2
           (λ (var2)
             (let ((var (gensym)))
               `(fresh ((,var : ,ty))
                  (conj (pairo ,var ,var1 ,var2)
                        ,(k var)))))))))))

(define (simp-vals vs tys k)
  (match* (vs tys)
    ((`() `()) (k '()))
    ((`(,v . ,vs^) `(,ty . ,tys^))
     (simp-val v ty
       (λ (var)
         (simp-vals vs^ tys^
           (λ (vars)
             (k `(,var . ,vars)))))))))

(define (simp-goal goal env)
  (match goal
    (`(conj ,g ,gs ...)
     `(conj ,@(map (λ (g) (simp-goal g env)) `(,g . ,gs))))
    (`(disj ,g ,gs ...)
     `(disj ,@(map (λ (g) (simp-goal g env)) `(,g . ,gs))))
    (`(fresh ((,vs : ,tys) ...) ,g ,gs ...)
     (let ((env^ (extend-env* vs tys env)))
       `(fresh (,@(map (λ (v t) `(,v : ,t)) vs tys))
          ,(simp-goal g env^)
          ,@(map (λ (g) (simp-goal g env^)) gs))))
    (`(== ,_ ,v1 ,v2) #:when (equal? v1 v2) 'succeed)
    (`(== ,ty ,v1 ,v2)
     (simp-val (eval-val v1) ty
       (λ (var1)
         (simp-val (eval-val v2) ty
           (λ (var2) `(== ,var1 ,var2))))))
    (`(=/= ,_ ,v1 ,v2) #:when (equal? v1 v2) 'fail)
    (`(=/= ,ty ,v1 ,v2)
     (simp-val (eval-val v1) ty
       (λ (var1)
         (simp-val (eval-val v2) ty
           (λ (var2) `(=/= ,var1 ,var2))))))
    (`(,R ,vs ...) #:when (symbol? R)
     (let ((tys (rel-type R env)))
       (simp-vals vs tys
         (λ (vars) `(,R ,@vars)))))))

(define (simp-def def env)
  (match def
    (`(defrel (,rel (,vs : ,tys) ...) ,g ,gs ...)
     #:when (symbol? rel)
     `(defrel (,rel ,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,@(map (λ (g) (simp-goal g (extend-env* vs tys env)))
            `(,g . ,gs))))
    (`(run ,n ((,vs : ,tys) ...) ,g ,gs ...)
     `(run ,n (,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,@(map (λ (g) (simp-goal g (extend-env* vs tys env)))
            `(,g . ,gs))))))

;;; Language 3
;;; A relation definition
;;; Rel := (defrel (Symbol (Symbol : vτ) ...) Goal ...)
;;;
;;; A goal
;;; Goal := (Symbol Symbol ...)
;;;      |  (conj Goal Goal ...)
;;;      |  (disj Goal Goal ...)
;;;      |  (== Symbol Symbol)
;;;      |  (=/= Symbol Symbol)
;;;      |  (fresh ((Symbol : vτ) ...) Goal Goal ...)
;;;      |  (soleo Symbol)
;;;      |  (lefto Symbol Symbol)
;;;      |  (righto Symbol Symbol)
;;;      |  (pairo Symbol Symbol Symbol)
;;;      |  succeed
;;;      |  fail
;;;
;;; A value type
;;; vτ  := Unit
;;;     |  (Pair vτ₁ vτ₂)
;;;     |  (Sum vτ₁ vτ₂)
;;;
;;; A query
;;; Query := (run n ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A program
;;; Prgm = Rel ... Query

;;; Pass 3: shorten goal
(define (comp-goal goal env)
  (match goal
    (`(conj ,g) (comp-goal g env))
    (`(conj ,g ,gs ...)
     `(conj ,(comp-goal g env) ,(comp-goal `(conj ,@gs) env)))
    (`(disj ,g) (comp-goal g env))
    (`(disj ,g ,gs ...)
     `(disj ,(comp-goal g env) ,(comp-goal `(disj ,@gs) env)))
    (`(fresh ((,v : ,ty)) ,g ,gs ...)
     `(fresh ((,v : ,ty))
        ,(comp-goal `(conj ,g ,@gs) env)))
    (`(fresh ((,vs : ,tys) ...) ,g ,gs ...)
     (foldr (λ (v t b)
              `(fresh ((,v : ,t)) ,b))
            (comp-goal `(conj ,g ,@gs) env)
            vs tys))
    (`(== ,_ ,_) goal)
    (`(=/= ,_ ,_) goal)
    (`(,R ,_ ...) #:when (symbol? R) goal)))

(define (comp-def def env)
  (match def
    (`(defrel (,rel (,vs : ,tys) ...) ,g ,gs ...)
     #:when (symbol? rel)
     `(defrel (,rel ,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,(comp-goal `(conj ,g ,@gs) (extend-env* vs tys env))))
    (`(run ,n ((,vs : ,tys) ...) ,g ,gs ...)
     `(run ,n (,@(map (λ (v t) `(,v : ,t)) vs tys))
        ,(comp-goal `(conj ,g ,@gs) (extend-env* vs tys env))))))

;;; Language 4
;;; A relation definition
;;; Rel := (defrel (Symbol (Symbol : vτ) ...) Goal)
;;;
;;; A goal
;;; Goal := (Symbol Symbol ...)
;;;      |  (conj Goal Goal)
;;;      |  (disj Goal Goal)
;;;      |  (== Symbol Symbol)
;;;      |  (=/= Symbol Symbol)
;;;      |  (fresh ((Symbol : vτ)) Goal)
;;;      |  (soleo Symbol)
;;;      |  (lefto Symbol Symbol)
;;;      |  (righto Symbol Symbol)
;;;      |  (pairo Symbol Symbol Symbol)
;;;      |  succeed
;;;
;;; A value type
;;; vτ  := Unit
;;;     |  (Pair vτ₁ vτ₂)
;;;     |  (Sum vτ₁ vτ₂)
;;;
;;; A query
;;; Query := (run n ((Symbol : vτ) ...) Goal)
;;;
;;; A program
;;; Prgm = Rel ... Query

;;; Pass 4: Print everything to Ocaml
(define indent-offset 2)
(define (make-indent indent)
  (make-string indent #\space))
(define (increase-indent indent)
  indent)

(define (print-type ty)
  (match ty
    (`Unit 'Unit)
    (`(Pair ,ty1 ,ty2)
     (format "Prod(~a, ~a)"
             (print-type ty1)
             (print-type ty2)))
    (`(Sum ,ty1 ,ty2)
     (format "Sum(~a, ~a)"
             (print-type ty1)
             (print-type ty2)))))

(define (print-var val env indent)
  (match (var-index-type val env)
    (`(,idx . ,ty)
     (format "~a(~a, ~a)" (make-indent indent) idx (print-type ty)))))

(define (print-goal goal env indent)
  (match goal
    (`(conj ,g1 ,g2)
     (format "~aConj(\n~a,\n~a)"
             (make-indent indent)
             (print-goal g1 env (increase-indent indent))
             (print-goal g2 env (increase-indent indent))))
    (`(disj ,g1 ,g2)
     (format "~aDisj(\n~a,\n~a)"
             (make-indent indent)
             (print-goal g1 env (increase-indent indent))
             (print-goal g2 env (increase-indent indent))))
    (`(fresh ((,v : ,ty)) ,g)
     (format "~aFresh(~a,\n~a)"
             (make-indent indent)
             (print-type ty)
             (print-goal g (extend-env v ty env)
                         (increase-indent indent))))
    (`(== ,var1 ,var2)
     (format "~aEqo(\n~a,\n~a)"
             (make-indent indent)
             (print-var var1 env (increase-indent indent))
             (print-var var2 env (increase-indent indent))))
    (`(=/= ,var1 ,var2)
     (format "~aNeqo(\n~a,\n~a)"
             (make-indent indent)
             (print-var var1 env (increase-indent indent))
             (print-var var2 env (increase-indent indent))))
    (`(soleo ,var)
     (format "~aSoleo(\n~a)"
             (make-indent indent)
             (print-var var env (increase-indent indent))))
    (`(lefto ,var1 ,var2)
     (format "~aLefto(\n~a,\n~a)"
             (make-indent indent)
             (print-var var1 env (increase-indent indent))
             (print-var var2 env (increase-indent indent))))
    (`(righto ,var1 ,var2)
     (format "~aRighto(\n~a,\n~a)"
             (make-indent indent)
             (print-var var1 env (increase-indent indent))
             (print-var var2 env (increase-indent indent))))
    (`(pairo ,var1 ,var2 ,var3)
     (format "~aPairo(\n~a,\n~a,\n~a)"
             (make-indent indent)
             (print-var var1 env (increase-indent indent))
             (print-var var2 env (increase-indent indent))
             (print-var var3 env (increase-indent indent))))
    (`succeed "Succeed")
    (`(,R ,vs ...)
     #:when (symbol? R)
     (format "~aRel(\"~a\",\n[~a])"
             (make-indent indent)
             R
             (print-list (add-between (map (λ (v) (print-var v env 0)) vs) "; "))))))

(define (print-def def env indent)
  (match def
    (`(defrel (,rel (,vs : ,tys) ...) ,g)
     #:when (symbol? rel)
     (format "let ~a : rel = {\n~aname = \"~a\";\n~aargs = [~a];\n~abody =\n~a};;\n\n"
             rel
             (make-indent indent) rel
             (make-indent indent)
             (print-list (add-between (map print-type tys) ";"))
             (make-indent indent)
             (print-goal g (extend-env* vs tys env) indent)))
    (`(run ,n ((,vs : ,tys) ...) ,g)
     (format "let ~a : tk_prgm = [\n~a~a;\n~a{\n~aname = \"maino\";\n~aargs = [~a];\n~abody =\n~a}];;\n\n"
             (gensym 'maino)
             (make-indent indent)
             (print-list (add-between (map (λ (rel) (format "~a" rel)) (all-rels env)) ";"))
             (make-indent indent)
             (make-indent indent)
             (make-indent indent)
             (print-list (add-between (map print-type tys) ";"))
             (make-indent indent)
             (print-goal g (extend-env* vs tys env) indent)))))

(define (print-list lst)
  (match lst
    (`() "")
    (`(,a . ,d)
     (string-append a (print-list d)))))

(define (compile-defs defs env)
  (match defs
    (`() '())
    (`(,def . ,defs^)
     (cons (print-def
            (comp-def
             (simp-def
              (eval-def def env) env)
             env)
            env
            indent-offset)
       (compile-defs defs^ env)))))

(define (to-ocaml defs)
  (let ((env (collect-names defs)))
    (compile-defs defs env)))

;;; The following program translates Language 1 to
;;; miniKanren
(define (to-mk-val v) v)

(define (to-mk-goal g)
  (match g
    (`(conj ,g ,gs ...)
     `(conj ,@(map (λ (g) (to-mk-goal g)) `(,g . ,gs))))
    (`(disj ,g ,gs ...)
     `(disj ,@(map (λ (g) (to-mk-goal g)) `(,g . ,gs))))
    (`(== ,_ ,v1 ,v2)
     `(== ,(to-mk-val v1) ,(to-mk-val v2)))
    (`(=/= ,_ ,v1 ,v2)
     `(=/= ,(to-mk-val v1) ,(to-mk-val v2)))
    (`(fresh ((,vs : ,tys) ...) ,g ,gs ...)
     `(fresh ,vs
        ,@(map (λ (g) (to-mk-goal g)) `(,g . ,gs))))
    (`(,R ,vs ...) #:when (symbol? R) `(,R ,@(map to-mk-val vs)))))

(define (to-mk-def def)
  (match def
    (`(defrel (,rel (,vs : ,tys) ...) ,g ,gs ...)
     #:when (symbol? rel)
     `(defrel (,rel ,@vs) ,(to-mk-goal g) ,@(map to-mk-goal gs)))
    (`(run ,n ((,vs : ,_) ...) ,g ,gs ...)
     `(run ,n ,vs
        ,(to-mk-goal g) ,@(map to-mk-goal gs)))))

(define (to-mk-defs defs)
  (match defs
    (`() '())
    (`(,def . ,defs^)
     (cons (to-mk-def def) (to-mk-defs defs^)))))

(define (to-mk defs)
  (to-mk-defs defs))
