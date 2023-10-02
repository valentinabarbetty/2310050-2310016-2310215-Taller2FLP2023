#lang eopl

;; Taller 2 FLP
;; Valentina Barbetty Arango 2310050
;; Brayan Julio Gomez Muñoz 2310016
;; Jheison Gomez Muñoz 2310215


;; -------------------------- GRAMÁTICA -------------------------

;;       <FNC> ::= <num_variables> (<Clausulas>)
;; <Clausulas-and> ::= (<Clausula-or>) | (<Clausula-or>) and <Clausulas-and>
;;  <Clausula-or> ::= <numero> |  <numero> or <Clausula-or>


;; **************** REPRESENTACIÓN CON LISTAS ****************

;;---------------------- CONSTRUCTORES -----------------------


;; <FNC> ::= <num_variables> (<Clausulas>)
(define FNC
  (lambda (num_variables clausulas)
    (list 'FNC num_variables clausulas)))

;; EJEMPLOS DE PRUEBAS
(FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6)))))


;; <Clausulas-and> ::= (<Clausula-or>) | (<Clausula-or>) and <Clausulas-and>
(define Clausulas-and
  (lambda (clausula-or clausulas)
    (if (null? clausulas)
        (list 'Clausulas-and clausula-or)
        (list 'Clausulas-and clausula-or clausulas))))

;;EJEMPLOS DE PRUEBAS
;;(Clausulas-and (Clausula-or 3 5) '())
;;(Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6)))


;; <Clausula-or> ::= <numero> | <numero> or <Clausula-or>
(define Clausula-or
  (lambda (numero clausula)
    (if (null? clausula)
        (list 'Clausula-or numero)
        (list 'Clausula-or numero clausula))))
;; EJEMPLOS DE PRUEBAS
(Clausula-or 3 '())
(Clausula-or 3 (Clausula-or 3 (Clausula-or 9 6)))

;;---------------------- EXTRACTORES -----------------------

;; EXTRACTORES
(define FNC->num_vars
  (lambda (l)
    (cadr l)))

;; EJEMPLOS PRUEBAS
(FNC->num_vars (FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6))))))


;; EXTRACTORES
(define FNC->clausulas
  (lambda (l)
    (caddr l)))

;; EJEMPLOS PRUEBAS
(FNC->clausulas (FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6))))))

;; EXTRACTORES
(define FNC->variables
  (lambda (l)
    (cond [(null? l) l]
          [(number? l) (list l)]
          [(eq? (car l) 'Clausula-or)
           (append (FNC->variables (cadr l)) (FNC->variables (caddr l)))]
          [else '()]
            )))

;; EJEMPLOS PRUEBAS
(FNC->variables (Clausula-or 3 (Clausula-or 9 (Clausula-or 5 6))))


;; CREACIÓN DE 3 INSTANCIAS SAT
(FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6)))))
(FNC 2 '((Clausulas-and (Clausula-or 1 2) (Clausulas-and (Clausula-or 2 (Clausula-or 1 -1))))))
(FNC 3 '((Clausulas-and (Clausula-or 3 6) (Clausulas-and (Clausula-or 2 (Clausula-or 1 (Clausula-or -1 3))) (Clausula-and (Clausula-or 2 3))))))



;; *************************************************** REPRESENTACIÓN CON DATA-TYPES ****************************************************


;;       <FNC> ::= <num_variables> (<Clausulas-and>)
;; <Clausulas-and> ::= (<Clausula-or>) | (<Clausula-or>) and <Clausulas-and>
;;  <Clausula-or> ::= <numero> |  <numero> or <Clausula-or>

;;FNC
(define-datatype SAT SAT?
  (fnc (num_variables number?)
       (clau clausulas?)
  ))

;; CASO AND
(define-datatype clausulas clausulas?
  (ors (orsi cor?)) ;; puede recibir solo una clausula or
  (ands
   (firstBody cor?)
   (restBody clausulas?)))

;; CASO BASE CON NUMERO Y CON OR ANIDADO
(define-datatype cor cor?
  (numero (num number?))
  (clausulaor
   (firstBody number?)
   (restBody cor?)))



;************************************* PARSE 
(define parser2
  (lambda (dato)
    (cond
         [(number? dato)
              (numero dato)]
         [(and (= (length dato) 1) (and (list? dato) (number? (car dato))))
          (parser2 (car dato))
         ]
         [(eqv? (car dato) 'fnc)
             (fnc (cadr dato) (parser2 (caddr dato)))]       
         [(eqv? (cadr dato) 'or)          
           (clausulaor (car dato) (parser2 (cddr dato)))]
         [(eqv? (cadr dato) 'and)
          (cond[(> (length dato) 3)
                 (ands (parser2 (car dato)) (parser2 (cddr dato)))]
               [else (ands (parser2 (car dato)) (ors (parser2 (caddr dato))))]
           )]
         )))

;*************************************  UNPARSE
(define unparser-cor
  (lambda (exp)
    (cases cor exp
      (numero (num) (list num))
      (clausulaor (firstBody restBody)
                  (append (list firstBody)
                          (list 'or)
                          (unparser-cor restBody))))))
(define unparser-and
  (lambda (exp)
    (cases clausulas exp
      (ors (orsi)
           (unparser-cor orsi))
      (ands
       (firstBody restBody)
       (append (list (unparser-cor firstBody))
             (list 'and)
             (list (unparser-and restBody))))
    )))

(define unparser
  (lambda (exp)
    (cases SAT exp
      (fnc (num_variables clau)
           (append (list 'FNC)
           (list num_variables)
           (list (unparser-and clau)))))))

;*************************************  MATRIZ
(define patron
  (lambda (tamano)
    (LxL tamano tamano)))

(define LxL
  (lambda (tamano longitud)
    (if (= longitud 0)
        '(())
        (append (append-v-resto (LxL tamano (- longitud 1)))
                (append-f-resto (LxL tamano (- longitud 1)))
                ))))

(define append-v-resto
  (lambda (resto)
    (if (null? resto)
        '()
        (cons (cons #t (car resto)) (append-v-resto (cdr resto))))))

(define append-f-resto
  (lambda (resto)
    (if (null? resto)
        '()
        (cons (cons #f (car resto)) (append-f-resto (cdr resto))))))


;*************************************** 

(define EVALUARSAT
  (lambda (l)
    (recursion (caddr l) (patron(FNC->num_vars l)))
  )
)

(define recursion
  (lambda (l matriz)
    (cond [(null? matriz) "insatisfactible"]
          [(if(evalu-and l (car matriz))
               (list "satisfactible" (car matriz))
              (recursion l (cdr matriz)))]
    )
  )
)

(define evalu-and
  (lambda (l matriz)
   (cond
     [(null? l) #f]
     [(number? (car l)) (convertir  l matriz)]
     [(eqv? 'Clausula-or (car l))
              (or (convertir (FNC->variables  l) matriz))]
     [(eqv? 'Clausulas-and (car l))
              (and (evalu-and (cadr l) matriz) (evalu-and (caddr l) matriz))]
    )
  )
)


;;evalua los or dentro de la lista (or v v f) = v
(define convertir
 (lambda (l matriz)
   (cond [(null? l) #f]
         [(> (car l) 0)
           (or (recorrer (car l)  matriz 1) (convertir (cdr l) matriz))]
         [else (or (not (recorrer (* (car l) -1) matriz 1)) (convertir (cdr l) matriz))]
   )
 )
)

;;Recorre matriz de v y f primera 
(define recorrer
  (lambda (l matriz contador)
   (cond [(null? matriz) #f]
          [(= l contador)  (car matriz)]
          [else (recorrer l (cdr matriz) (+ contador 1))]
       )
     )
  )


(define fnc-ejemplo '(fnc 2 (Clausula-or 1 (Clausula-or 2 1))))
(define fnc-ejemplo2
  '(fnc 2 (Clausulas-and
           (Clausula-or 1 2)
           (Clausulas-and
            (Clausula-or -1 '()) (Clausula-or -2 '())))))


(define fnc-ejemplo3
  '(fnc 4 (Clausulas-and
           (Clausula-or 1 (Clausula-or -2
                                       (Clausula-or 3
                                                    4)))
           (Clausulas-and
            (Clausula-or -2 3) (Clausulas-and (Clausula-or -1 (Clausula-or -2 -3))
                                              (Clausula-and (Clausula-or 3 4) (2)))))))
(define fnc-ejemplo4
  '(fnc 4 (Clausulas-and
           (Clausula-or 1 (Clausula-or -2
                                       3))
           (Clausulas-and
            (Clausula-or 3 -4) (Clausulas-and (Clausula-or -1 (Clausula-or 3 -4))
                                              (-3))))))