#lang eopl

;; Taller 2 FLP
;; Valentina Barbetty Arango 2310050
;; Brayan Julio Gomez Muñoz 2310016
;; Jheison Gomez Muñoz 2310215


;; https://github.com/valentinabarbetty/2310050-2310016-2310215-Taller2FLP2023.git


;; -------------------------- GRAMÁTICA -------------------------

;;       <FNC> ::= <num_variables> (<Clausulas>)
;; <Clausulas-and> ::= (<Clausula-or>) | (<Clausula-or>) and <Clausulas-and>
;;  <Clausula-or> ::= <numero> |  <numero> or <Clausula-or>



;; **************** REPRESENTACIÓN CON LISTAS ****************

;;---------------------- CONSTRUCTORES -----------------------


;; <FNC> ::= <num_variables> (<Clausulas>)

;; CONSTRUCTOR FNC
(define FNC
  (lambda (num_variables clausulas)
    (list 'FNC num_variables clausulas)))

;; EJEMPLOS DE PRUEBAS
(FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6)))))

;--------------------

;; <Clausulas-and> ::= (<Clausula-or>) | (<Clausula-or>) and <Clausulas-and>
;; CONSTRUCTOR AND
(define Clausulas-and
  (lambda (clausula-or clausulas)
    (if (null? clausulas)
        (list 'Clausulas-and clausula-or)
        (list 'Clausulas-and clausula-or clausulas))))

;;EJEMPLOS DE PRUEBAS
;;(Clausulas-and (Clausula-or 3 5) '())
;;(Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6)))

;; ---------------------------


;; <Clausula-or> ::= <numero> | <numero> or <Clausula-or>
;;CONSTRUCTOR OR

(define Clausula-or
  (lambda (numero clausula)
    (if (null? clausula)
        (list 'Clausula-or numero)
        (list 'Clausula-or numero clausula))))
;; EJEMPLOS DE PRUEBAS
(Clausula-or 3 '())
(Clausula-or 3 (Clausula-or 3 (Clausula-or 9 6)))



;;---------------------- EXTRACTORES -----------------------

;; EXTRACTORES NUMERO VARIABLES
(define FNC->num_vars
  (lambda (l)
    (cadr l)))

;; EJEMPLOS PRUEBAS
(FNC->num_vars (FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6))))))



;; ---------------------
;; EXTRACTORES CLAUSULAS
(define FNC->clausulas
  (lambda (l)
    (caddr l)))

;; EJEMPLOS PRUEBAS
(FNC->clausulas (FNC 4 '((Clausulas-and (Clausula-or 3 5) (Clausulas-and (Clausula-or 9 6))))))


;; ---------------------
;; EXTRACTORES VARIABLES
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








;; ************************************ REPRESENTACIÓN CON DATA-TYPES ****************************************************


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



;; CREACIÓN DE 3 INSTANCIAS SAT
(fnc 8 (ands (numero 6)
             (ands (clausulaor 4 (numero 2)) (ors (numero 3)))))

(fnc 2 (ors (clausulaor 5 (numero 3))))

(fnc 3 (ands (numero 6)
             (ands (clausulaor 4 (numero 2))
                   (ands (clausulaor 1
                                     (clausulaor 2 (numero 1)))
                         (ors (numero 2))))))




;************************************* PARSE **************************************
;; La funcion PARSEBNF es encargada de analizar e intérpretar notaciónes BFN,
;; y su función principal es dirigir el flujo de procesamiento de acuerdo con la estructura de la expresión BNF que recibe como entrada.
;;Su objetivo general es traducir expresiones en una notación específica BFN en un formato o acción específica de árbol de sintaxis abstracta.

(define PARSEBNF
  (lambda (dato)
    (cond
         [(number? dato)
              (numero dato)]
         [(and (= (length dato) 1) (and (list? dato) (number? (car dato))))
          (PARSEBNF (car dato))
         ]
         [(eqv? (car dato) 'fnc)
             (fnc (cadr dato) (PARSEBNF (caddr dato)))]       
         [(eqv? (cadr dato) 'or)          
           (clausulaor (car dato) (PARSEBNF (cddr dato)))]
         [(eqv? (cadr dato) 'and)
          (cond[(> (length dato) 3)
                 (ands (PARSEBNF (car dato)) (PARSEBNF (cddr dato)))]
               [else (ands (PARSEBNF (car dato)) (ors (PARSEBNF (caddr dato))))]
           )]
         )))


;; EJEMPLOS DE PRUEBAS
(PARSEBNF '(fnc 5 ((1 or 2 or 3) and (4 or 5 or 6))))
(PARSEBNF '(fnc 5 ((1 or 2 or 3) and (4 or 5 or 6) and (1))))




;*************************************  UNPARSE

;;La funcion UNPARSEBNF es la encargada de tomar un árbol de sintaxis abstracta y lo transforma en listas legibles y de fácil comprensión.
;;Esta función utiliza datatypes previamente definidos para llevar a cabo la tarea. Su objetivo principal es convertir
;;la representación interna del código fuente, en forma de un árbol de sintaxis abstracta, de vuelta al código fuente original,
;;lo que facilita su lectura y comprensión.
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

(define UNPARSEBNF
  (lambda (exp)
    (cases SAT exp
      (fnc (num_variables clau)
           (append (list 'FNC)
           (list num_variables)
           (list (unparser-and clau)))))))



;; EJEMPLOS DE PRUEBA
(UNPARSEBNF (fnc 3 (ands (numero 6)
             (ands (clausulaor 4 (numero 2))
                   (ands (clausulaor 1
                                     (clausulaor 2 (numero 1)))
                         (ors (numero 2)))))))

(UNPARSEBNF (fnc 2 (ors (clausulaor 5 (numero 3)))))









;; **************************** CODIGO CLIENTE ************


;;*************************************  MATRIZ F y V
;;Esta función genera una matriz de valores 'V' y 'F' basada en el número de variables ingresadas en la expresión
;;en Forma Normal Conjuntiva (FNC). Por ejemplo, si se llama con 'patron 2', devuelve '((vv)(vf)(fv)(ff))'.

(define patron
  (lambda (tamano)
    (LxL tamano tamano)))

;;La función LxL toma dos argumentos, tamano y longitud, y crea un patrón de listas anidadas de tamaño
;;tamano por longitud. Utiliza recursión para construir el patrón llamando a las funciones append-v-resto
;;y append-f-resto en cada iteración.
(define LxL
  (lambda (tamano longitud)
    (if (= longitud 0)
        '(())
        (append (append-v-resto (LxL tamano (- longitud 1)))
                (append-f-resto (LxL tamano (- longitud 1)))
                ))))

;;Las funciones append-v-resto y append-f-resto toman una lista resto y agregan elementos
;;#t (verdadero) o #f (falso) al principio de cada sublista en resto, creando así un patrón
;;de valores verdaderos o falsos en función de la entrada

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


;; EJEMPLOS DE PRUEBA
(patron 2) 
(patron 4)

;*************************************** EVALUACIÓN DE INSTANCIAS SAT
;Introduce una función en Forma Normal Conjuntiva (FNC) que será evaluada para
;determinar si es satisfacible o insatisfacible.

(define EVALUARSAT
  (lambda (l)
    (recursion (caddr l) (patron(FNC->num_vars l)))
  )
)
;Esta función auxiliar se encarga de realizar recursión con las diversas combinaciones del patrón.
(define recursion
  (lambda (l matriz)
    (cond [(null? matriz) "insatisfactible"]
          [(if(evalu-and l (car matriz))
               (list "satisfactible" (car matriz))
              (recursion l (cdr matriz)))]
    )
  )
)
;Esta función tiene la responsabilidad de extraer los elementos de la función FNC utilizando
;los extractores y ejecutar las operaciones lógicas "OR" y "AND" según corresponda.
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


;;Esta función tiene la tarea de llevar a cabo la operación "OR" dentro de la función
;;FNC y, al mismo tiempo, verifica si un número es negativo para cambiar la respuesta
;; de "Verdadero" a "Falso" o de "Falso" a "Verdadero
(define convertir
 (lambda (l matriz)
   (cond [(null? l) #f]
         [(> (car l) 0)
           (or (recorrer (car l)  matriz 1) (convertir (cdr l) matriz))]
         [else (or (not (recorrer (* (car l) -1) matriz 1)) (convertir (cdr l) matriz))]
   )
 )
)

;;El propósito de esta función es extraer el valor en la posición correspondiente de la matriz
;;de valores verdaderos y falsos, según el número ingresado.
;;Por ejemplo, si se ingresa el número 2 y la lista es '(V F)', la función retornará
;;'F', ya que 'F' se encuentra en la posición 2.
(define recorrer
  (lambda (l matriz contador)
   (cond [(null? matriz) #f]
          [(= l contador)  (car matriz)]
          [else (recorrer l (cdr matriz) (+ contador 1))]
       )
     )
  )




;; ************************* EJEMPLOS DE PRUEBAS
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