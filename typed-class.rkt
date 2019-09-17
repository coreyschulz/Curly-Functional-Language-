#lang plait

(require "class.rkt"
         "inherit.rkt")

(define-type ClassT
  (classT [super-name : Symbol]
          [fields : (Listof (Symbol * Type))]
          [methods : (Listof (Symbol * MethodT))]))

(define-type MethodT
  (methodT [arg-type : Type]
           [result-type : Type]
           [body-expr : ExpI])) 

(define-type Type
  (numT)
  (nullT) 
  (objT [class-name : Symbol]))

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(define (get-all-field-types class-name t-classes)
  (if (equal? class-name 'Object)
      empty        
      (type-case ClassT (find t-classes class-name)
        [(classT super-name fields methods)
         (append 
          (get-all-field-types super-name t-classes)
          (map snd fields))])))

;; ----------------------------------------

(define (make-find-in-tree class-items)
  (lambda (name class-name t-classes)
    (local [(define t-class (find t-classes class-name))
            (define items (class-items t-class))
            (define super-name 
              (classT-super-name t-class))]
      (if (equal? super-name 'Object)
          (find items name)
          (try (find items name)
               (lambda ()
                 ((make-find-in-tree class-items)
                  name 
                  super-name
                  t-classes)))))))

(define find-field-in-tree
  (make-find-in-tree classT-fields))

(define find-method-in-tree
  (make-find-in-tree classT-methods))

;; ----------------------------------------

(define (is-subclass? name1 name2 t-classes)
  (cond
    [(equal? name1 name2) #t]
    [(equal? name1 'Object) #f]
    [else
     (type-case ClassT (find t-classes name1)
       [(classT super-name fields methods)
        (is-subclass? super-name name2 t-classes)])]))

(define (is-subtype? t1 t2 t-classes)
  (type-case Type t1
    [(objT name1)
     (type-case Type t2 
       [(objT name2)
        (is-subclass? name1 name2 t-classes)]
       [(nullT) #t]
       [else #f])]
    [(nullT) #t]
    [else (equal? t1 t2)]))

(module+ test
  (define a-t-class (values 'A (classT 'Object empty empty)))
  (define b-t-class (values 'B (classT 'A empty empty)))

  (test (is-subclass? 'Object 'Object empty)
        #t)
  (test (is-subclass? 'A 'B (list a-t-class b-t-class))
        #f)
  (test (is-subclass? 'B 'A (list a-t-class b-t-class))
        #t)

  (test (is-subtype? (numT) (numT) empty)
        #t)
  (test (is-subtype? (numT) (objT 'Object) empty)
        #f)
  (test (is-subtype? (objT 'Object) (numT) empty)
        #f)
  (test (is-subtype? (objT 'A) (objT 'B) (list a-t-class b-t-class))
        #f)
  (test (is-subtype? (objT 'B) (objT 'A) (list a-t-class b-t-class))
        #t))

;; ----------------------------------------

(define typecheck-expr : (ExpI (Listof (Symbol * ClassT)) Type Type Boolean -> Type) 
  (lambda (expr t-classes this-type arg-type pass-bool)
    (local [(define (recur expr)
              (typecheck-expr expr t-classes this-type arg-type pass-bool))
            (define (typecheck-nums l r)
              (type-case Type (recur l)
                [(numT)
                 (type-case Type (recur r)
                   [(numT) (numT)]
                   [else (type-error r "num")])]
                [else (type-error l "num")]))]
      (type-case ExpI expr
        [(numI n) (numT)]
        [(nullI) (nullT)]
        [(plusI l r) (typecheck-nums l r)] 
        [(multI l r) (typecheck-nums l r)]
        [(argI) ;; added for part 1! 
         (if pass-bool
             (error 'typecheck "cannot use arg in main expression!")
             arg-type)]
        [(thisI) ;; also added for part 1! 
         (if pass-bool
             (error 'typecheck "cannot use this in main expression!") 
             this-type)]
        [(newI class-name exprs)
         (local [(define arg-types (map recur exprs))
                 (define field-types
                   (get-all-field-types class-name t-classes))]
           (if (and (= (length arg-types) (length field-types))
                    (foldl (lambda (b r) (and r b))
                           #t
                           (map2 (lambda (t1 t2) 
                                   (is-subtype? t1 t2 t-classes)) ;; fixed for part 4 to allow null. 
                                 arg-types
                                 field-types)))
               (objT class-name)
               (type-error expr "field type mismatch")))]
        [(getI obj-expr field-name)
         (type-case Type (recur obj-expr)
           [(objT class-name)
            (find-field-in-tree field-name
                                class-name
                                t-classes)]
           [else (type-error obj-expr "object")])]
[(sendI obj-expr method-name arg-expr)
         (local [(define obj-type (recur obj-expr))
                 (define arg-type (recur arg-expr))]
           (type-case Type obj-type
             [(objT class-name)
              (typecheck-send class-name method-name
                              arg-expr arg-type
                              t-classes)]
             [else
              (type-error obj-expr "object")]))]
        [(superI method-name arg-expr)
         (local [(define arg-type (recur arg-expr))
                 (define this-class
                   (find t-classes (objT-class-name this-type)))]
               (typecheck-send (classT-super-name this-class)
                               method-name
                               arg-expr arg-type
                               t-classes))]
        [(castI name oe)
         (if (equal? (nullT) (recur oe))
             (objT name)
             (local [(define object-name (objT-class-name (recur oe)))] ;; null is allowed as oe b/c of fix to is-subclass.
               (if (or (is-subclass? object-name name t-classes) (is-subclass? name object-name t-classes))
                   (objT object-name)
                   (type-error oe "object"))))]
        
        [(if0I cond fst snd)
         (let ([cond-type (recur cond)]
               [fst-type (recur fst)]
               [snd-type (recur snd)])
           (type-case Type cond-type
             [(numT)
              (least-upper-bound expr fst-type snd-type t-classes)]
             [else (type-error cond "number")]))]))))

(define (least-upper-bound [e : ExpI] [a-type : Type] [b-type : Type] [t-classes : (Listof (Symbol * ClassT))]) : Type 
  (type-case Type a-type
    [(numT)
     (type-case Type b-type
       [(numT) (numT)]
       [else (type-error e "doesn't match")])]
    [(objT a-name)
     (type-case Type b-type
       [(objT b-name) (objT (find-closest b-name (get-super-list a-name t-classes empty) t-classes))]
       [else (type-error e "doesn't match")])]
    [(nullT)
     (type-case Type b-type
       [(nullT) (nullT)]
       [else (type-error e "doesn't match")])])) 

(define (get-super-list [obj-name : Symbol] [t-classes : (Listof (Symbol * ClassT))] [returner : (Listof Symbol)]) : (Listof Symbol)
  (type-case ClassT (find t-classes obj-name)
    [(classT super-name fields methods)
     (if (symbol=? 'Object super-name)
         (reverse (cons 'Object (cons obj-name returner)))
         (get-super-list super-name t-classes (cons obj-name returner)))])) 

(define (find-closest [b-name : Symbol] [a-syms : (Listof Symbol)] [t-classes : (Listof (Symbol * ClassT))]) : Symbol
   (if (member b-name a-syms)
       b-name
       (type-case ClassT (find t-classes b-name)
         [(classT super-name fields methods)
          (find-closest super-name a-syms t-classes)])))


(define (typecheck-send [class-name : Symbol]
                        [method-name : Symbol]
                        [arg-expr : ExpI]
                        [arg-type : Type]
                        [t-classes : (Listof (Symbol * ClassT))])
  (type-case MethodT (find-method-in-tree
                      method-name
                      class-name
                      t-classes)
    [(methodT arg-type-m result-type body-expr)
     (if (is-subtype? arg-type arg-type-m t-classes)
         result-type
         (type-error arg-expr (to-string arg-type-m)))]))

(define (typecheck-method [method : MethodT]
                          [this-type : Type]
                          [t-classes : (Listof (Symbol * ClassT))]) : ()
  (type-case MethodT method
    [(methodT arg-type result-type body-expr)
     (if (is-subtype? (typecheck-expr body-expr t-classes
                                      this-type arg-type #f)
                      result-type
                      t-classes)
         (values)
         (type-error body-expr (to-string result-type)))]))

(define (check-override [method-name : Symbol]
                        [method : MethodT]
                        [this-class : ClassT]
                        [t-classes : (Listof (Symbol * ClassT))])
  (local [(define super-name 
            (classT-super-name this-class))
          (define super-method
            (try
             ;; Look for method in superclass:
             (find-method-in-tree method-name
                                  super-name
                                  t-classes)
             ;; no such method in superclass:
             (lambda () method)))]
    (if (and (equal? (methodT-arg-type method)
                     (methodT-arg-type super-method))
             (equal? (methodT-result-type method)
                     (methodT-result-type super-method)))
        (values)
        (error 'typecheck (string-append
                           "bad override of "
                           (to-string method-name))))))

(define (typecheck-class [class-name : Symbol]
                         [t-class : ClassT]
                         [t-classes : (Listof (Symbol * ClassT))])
  (type-case ClassT t-class
    [(classT super-name fields methods)
     (map (lambda (m)
            (begin
              (typecheck-method (snd m) (objT class-name) t-classes)
              (check-override (fst m) (snd m) t-class t-classes)))
          methods)]))

(define (typecheck [a : ExpI]
                   [t-classes : (Listof (Symbol * ClassT))]) : Type
  (begin
    (map (lambda (tc)
           (typecheck-class (fst tc) (snd tc) t-classes))
         t-classes)
    (typecheck-expr a t-classes (objT 'Object) (numT) #t)))

;; ----------------------------------------

(module+ test
  (define posn-t-class
    (values 'Posn
            (classT 'Object
                    (list (values 'x (numT)) (values 'y (numT)))
                    (list (values 'mdist
                                  (methodT (numT) (numT) 
                                           (plusI (getI (thisI) 'x) (getI (thisI) 'y))))
                          (values 'addDist
                                  (methodT (objT 'Posn) (numT)
                                           (plusI (sendI (thisI) 'mdist (numI 0))
                                                  (sendI (argI) 'mdist (numI 0)))))))))

  (define posn3D-t-class 
    (values 'Posn3D
            (classT 'Posn
                    (list (values 'z (numT)))
                    (list (values 'mdist
                                  (methodT (numT) (numT)
                                           (plusI (getI (thisI) 'z) 
                                                  (superI 'mdist (argI)))))))))

  (define square-t-class 
    (values 'Square
            (classT 'Object
                    (list (values 'topleft (objT 'Posn)))
                    (list))))

  (define cube-t-class
    (values 'Cube
            (classT 'Square
                     (list (values 'topright (objT 'Posn)))
                     (list))))

  (define quad-t-class
    (values 'Quad
            (classT 'Object
                    (list)
                    (list))))

      (define posn3D-t-class-null-ver 
      (values 'Posn3D-null
              (classT 'Posn3D
                      (list (values 'z (numT)))
                      (list (values 'mdist
                                    (methodT (numT) (numT)
                                             (plusI (getI (thisI) 'z) 
                                                    (superI 'mdist (nullI))))))))) ;; this is okay too.

  (define (typecheck-posn a)
    (typecheck a
               (list posn-t-class posn3D-t-class square-t-class cube-t-class quad-t-class posn3D-t-class-null-ver)))
  
  (define new-posn27 (newI 'Posn (list (numI 2) (numI 7))))
  (define new-posn531 (newI 'Posn3D (list (numI 5) (numI 3) (numI 1))))

  (test (typecheck-posn (sendI new-posn27 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI new-posn531 'mdist (numI 0)))
        (numT))  
  (test (typecheck-posn (sendI new-posn531 'addDist new-posn27))
        (numT))  
  (test (typecheck-posn (sendI new-posn27 'addDist new-posn531))
        (numT))

  (test (typecheck-posn (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1))))))
        (objT 'Square))
  (test (typecheck-posn (newI 'Square (list (newI 'Posn3D (list (numI 0) (numI 1) (numI 3))))))
        (objT 'Square))
  
  (test (typecheck (multI (numI 1) (numI 2))
                   empty)
        (numT))

  ;; PART 1 TESTS
  (test/exn (typecheck (multI (thisI) (numI 2))
                   empty)
        "cannot use this in main expression!")

  (test/exn (typecheck (multI (argI) (numI 2))
                   empty)
        "cannot use arg in main expression!")
                   
  (test/exn (typecheck-posn (sendI (thisI) 'mdist (numI 0)))
            "cannot use this in main expression!")

  (test/exn (typecheck-posn (sendI new-posn27 'mdist (argI)))
        "cannot use arg in main expression!")

  ;; PART 2 TESTS
  
  (test (typecheck-posn (castI 'Square (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1)))))))
        (objT 'Square))
  (test (typecheck-posn (castI 'Cube (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1)))))))
        (objT 'Square))
  (test/exn (typecheck-posn (castI 'Quad (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1)))))))
        "no type")

  ;; PART 3 TESTS

  (test (get-super-list 'Cube (list posn-t-class posn3D-t-class square-t-class cube-t-class quad-t-class) empty)
        (list 'Cube 'Square 'Object))

  (test (typecheck-posn (if0I (numI 0) (newI 'Posn (list (numI 0) (numI 1))) (newI 'Quad empty)))
        (objT 'Object))

  (test (typecheck-posn (if0I (numI 0) (newI 'Posn (list (numI 0) (numI 1))) (newI 'Posn (list (numI 0) (numI 0)))))
        (objT 'Posn))

  (test/exn (typecheck-posn (if0I (numI 0) (numI 0) (newI 'Posn (list (numI 0) (numI 0)))))
        "no type")

  (test/exn (typecheck-posn (if0I (newI 'Posn (list (numI 0) (numI 0))) (numI 0) (newI 'Posn (list (numI 0) (numI 0)))))
        "no type")

    (test/exn (typecheck-posn (if0I (numI 0) (newI 'Posn (list (numI 0) (numI 0))) (numI 0)))
        "no type")

      (test (typecheck-posn (if0I (numI 0) (numI 0) (numI 0)))
        (numT))

  ;; PART 4 TESTS

  (test/exn (typecheck-posn (plusI (nullI) (nullI)))
            "no type")

  (test/exn (typecheck-posn (multI (nullI) (nullI)))
            "no type")

  (test (least-upper-bound (numI 5) (nullT) (nullT) empty)
            (nullT))

  (test/exn (least-upper-bound (numI 5) (numT) (nullT) empty)
            "doesn't match")

  (test/exn (least-upper-bound (numI 5) (nullT) (numT) empty)
            "doesn't match")

  (test/exn (typecheck-posn (sendI (nullI) 'm (numI 0))) ;; nullI not allowed as object like this. 
        "no type")

  (test/exn (typecheck-posn (getI (nullI) 'x))
            "no type") ;; ...same here!

  (test/exn (typecheck-posn (if0I (numI 0) (nullI) (newI 'Posn (list (numI 0) (numI 0)))))
        "doesn't match") ;; because objT isn't the same as nullT, thus typecheck should reject.

  (test (typecheck-posn (sendI new-posn27 'addDist (nullI)))
        (numT)) ;; so typecheck allows, return the type of the caller if nullI. 

  (test/exn (typecheck-posn (sendI new-posn27 'addDist (numI 5)))
        "no type")
  
    (test (typecheck-posn (castI 'Cube (nullI)))
        (objT 'Cube))

  (test (typecheck-posn (castI 'Cube (newI 'Square (list (nullI))))) ;; want to allow nullT use in 
        (objT 'Square))

  (test (is-subtype? (objT 'hachi) (nullT) empty) ;; We want to allow nullT as always true as to not throw
        #t)   ;; ...off typechecker!

    (define new-posn27-null (newI 'Posn (list (nullI) (nullI))))

  (test (typecheck-posn new-posn27-null)
        (objT 'Posn))

  (test (typecheck-posn (sendI new-posn531 'addDist (nullI)))
        (numT)) 

  


  


  
  
  

  (test/exn (typecheck-posn (sendI (numI 10) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (sendI new-posn27 'mdist new-posn27))
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object empty))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (newI 'Object empty) (numI 1))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object (list (numI 1))))
                       empty)
            "no type")
  (test/exn (typecheck (getI (numI 1) 'x)
                       empty)
            "no type")
  (test/exn (typecheck (numI 10)
                       (list posn-t-class
                             (values 'Other
                                     (classT 'Posn
                                             (list)
                                             (list (values 'mdist
                                                           (methodT (objT 'Object) (numT)
                                                                    (numI 10))))))))
            "bad override")
  (test/exn (typecheck-method (methodT (numT) (objT 'Object) (numI 0)) (objT 'Object) empty)
            "no type")
  (test/exn (typecheck (numI 0)
                       (list square-t-class
                             (values 'Cube
                                     (classT 'Square
                                             empty
                                             (list
                                              (values 'm
                                                      (methodT (numT) (numT)
                                                               ;; No such method in superclass:
                                                               (superI 'm (numI 0)))))))))
            "not found")

  )

;; ----------------------------------------

(define strip-types : (ClassT -> ClassI)
  (lambda (t-class)
    (type-case ClassT t-class
      [(classT super-name fields methods)
       (classI
        super-name
        (map fst fields)
        (map (lambda (m)
               (values (fst m)
                       (type-case MethodT (snd m)
                         [(methodT arg-type result-type body-expr)
                          body-expr])))
             methods))])))
  
(define interp-t : (ExpI (Listof (Symbol * ClassT)) -> Value)
  (lambda (a t-classes)
    (interp-i a
              (map (lambda (c)
                     (values (fst c) (strip-types (snd c))))
                   t-classes))))

(module+ test
  (define (interp-t-posn a)
    (interp-t a
              (list posn-t-class posn3D-t-class)))
  
  (test (interp-t-posn (sendI new-posn27 'mdist (numI 0)))
        (numV 9))  
  (test (interp-t-posn (sendI new-posn531 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI new-posn531 'addDist new-posn27))
        (numV 18))
  (test (interp-t-posn (sendI new-posn27 'addDist new-posn531))
        (numV 18)))
