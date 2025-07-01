#lang racket
(require "translator.rkt")

;;; Below we use
;;; 0 for (Left Unit)
;;; 1 for (Right (Left Unit))
;;; 2 for (Right (Right (Left Unit)))
;;; 3 for (Right (Right (Right Unit)))

;;; Shorthand for types
(define num
  `(Sum Unit (Sum Unit (Sum Unit Unit))))

(define row
  `(Pair ,num (Pair ,num (Pair ,num ,num))))

(define plate
  `(Pair ,row (Pair ,row (Pair ,row ,row))))


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
;;;     |  (Pair τ₁ τ₂)
;;;     |  (Sum τ₁ τ₂)
;;;
;;; A query
;;; Query := (run n ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A program
;;; Prgm = Rel ... Query
(define diff
  `((defrel (diffo (n : ,num) (o : ,num))
      (=/= ,num n o)
      #;
      (disj
        (conj (== ,num n 0) (disj (== ,num o 1) (== ,num o 2) (== ,num o 3)))
        (conj (== ,num n 1) (disj (== ,num o 0) (== ,num o 2) (== ,num o 3)))
        (conj (== ,num n 2) (disj (== ,num o 0) (== ,num o 1) (== ,num o 3)))
        (conj (== ,num n 3) (disj (== ,num o 0) (== ,num o 1) (== ,num o 2)))))

    ;;; Running a goal
    (run 1 ((a : ,num)) (diffo 1 a))))

(define sudoku
  `((defrel (diffo (n : ,num) (o : ,num))
      (=/= ,num n o)
      #;
      (disj
        (=/= ,num n o)
        (conj (== ,num n 0) (disj (== ,num o 1) (== ,num o 2) (== ,num o 3)))
        (conj (== ,num n 1) (disj (== ,num o 0) (== ,num o 2) (== ,num o 3)))
        (conj (== ,num n 2) (disj (== ,num o 0) (== ,num o 1) (== ,num o 3)))
        (conj (== ,num n 3) (disj (== ,num o 0) (== ,num o 1) (== ,num o 2)))))

    (defrel (valid_4x4 (a : ,num) (b : ,num) (c : ,num) (d : ,num))
      (conj
        (diffo a b)
        (diffo a c)
        (diffo a d)
        (diffo b c)
        (diffo b d)
        (diffo c d)))

    (defrel (sudoku_4x4
             (a : ,num) (b : ,num) (c : ,num) (d : ,num)
             (e : ,num) (f : ,num) (g : ,num) (h : ,num)
             (i : ,num) (j : ,num) (k : ,num) (l : ,num)
             (m : ,num) (n : ,num) (o : ,num) (p : ,num))
      (conj
        (valid_4x4 a b c d)
        (valid_4x4 a b e f)
        (valid_4x4 a e i m)
        (valid_4x4 i j m n)
        (valid_4x4 i j k l)
        (valid_4x4 k l o p)
        (valid_4x4 m n o p)
        (valid_4x4 b f j n)
        (valid_4x4 e f g h)
        (valid_4x4 c d g h)
        (valid_4x4 d h l p)
        (valid_4x4 c g k o)
        ))

    ;;; Running a goal
    (run 1 ((a : ,num) (b : ,num) (c : ,num) (d : ,num)
            (e : ,num) (f : ,num) (g : ,num) (h : ,num)
            (i : ,num) (j : ,num) (k : ,num) (l : ,num)
            (m : ,num) (n : ,num) (o : ,num) (p : ,num))
      (sudoku_4x4 3 b 0 d e f g h i j k l m 0 o 2))))
