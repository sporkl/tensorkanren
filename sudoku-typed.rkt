#lang racket
(require "translator.rkt")

;;; Below we use
;;; 0 for (Left Unit)
;;; 1 for (Right (Left Unit))
;;; 2 for (Right (Right (Left Unit)))
;;; 3 for (Right (Right (Right Unit)))

;;; A type definition
;;; Type := (define name τ)
;;;
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
;;; vτ := Symbol | τ
;;;
;;; A primitive type
;;; τ := Unit
;;;   | (Pair τ₁ τ₂)
;;;   | (Sum τ₁ τ₂)
;;;
;;; A query
;;; Query := (run n ((Symbol : vτ) ...) Goal Goal ...)
;;;
;;; A program
;;; Prgm = Type ... Rel ... Query
(define diff
  `((define n4
      (Sum Unit (Sum Unit (Sum Unit Unit))))

    (defrel (diffo (n : n4) (o : n4))
      (=/= n4 n o))

    ;;; Running a goal
    (run 1 ((a : n4)) (diffo 1 a))))

(define sudoku4
  `((define n4
      (Sum Unit (Sum Unit (Sum Unit Unit))))

    (defrel (diffo (n : n4) (o : n4))
      (=/= n4 n o))

    (defrel (valid_4x4 (a : n4) (b : n4) (c : n4) (d : n4))
      (conj
        (diffo a b)
        (diffo a c)
        (diffo a d)
        (diffo b c)
        (diffo b d)
        (diffo c d)))

    (defrel (sudoku_4x4
             (a : n4) (b : n4) (c : n4) (d : n4)
             (e : n4) (f : n4) (g : n4) (h : n4)
             (i : n4) (j : n4) (k : n4) (l : n4)
             (m : n4) (n : n4) (o : n4) (p : n4))
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
    (run 1 ((a : n4) (b : n4) (c : n4) (d : n4)
            (e : n4) (f : n4) (g : n4) (h : n4)
            (i : n4) (j : n4) (k : n4) (l : n4)
            (m : n4) (n : n4) (o : n4) (p : n4))
      (sudoku_4x4 3 b 0 d e f g h i j k l m 0 o 2))))

(define sudoku9
  `((define n9
      (Sum Unit (Sum Unit (Sum Unit (Sum Unit (Sum Unit (Sum Unit (Sum Unit (Sum Unit Unit)))))))))

    (defrel (diffo (n : n9) (o : n9))
      (=/= n9 n o))

    (defrel
      (valid_9x9
       (r1 : n9) (r2 : n9) (r3 : n9) (r4 : n9) (r5 : n9) (r6 : n9) (r7 : n9) (r8 : n9) (r9 : n9))
      (diffo r1 r2)
      (diffo r1 r3)
      (diffo r1 r4)
      (diffo r1 r5)
      (diffo r1 r6)
      (diffo r1 r7)
      (diffo r1 r8)
      (diffo r1 r9)
      (diffo r2 r3)
      (diffo r2 r4)
      (diffo r2 r5)
      (diffo r2 r6)
      (diffo r2 r7)
      (diffo r2 r8)
      (diffo r2 r9)
      (diffo r3 r4)
      (diffo r3 r5)
      (diffo r3 r6)
      (diffo r3 r7)
      (diffo r3 r8)
      (diffo r3 r9)
      (diffo r4 r5)
      (diffo r4 r6)
      (diffo r4 r7)
      (diffo r4 r8)
      (diffo r4 r9)
      (diffo r5 r6)
      (diffo r5 r7)
      (diffo r5 r8)
      (diffo r5 r9)
      (diffo r6 r7)
      (diffo r6 r8)
      (diffo r6 r9)
      (diffo r7 r8)
      (diffo r7 r9)
      (diffo r8 r9))

    (defrel
      (sudoku_9x9
       (r11 : n9) (r12 : n9) (r13 : n9) (r14 : n9) (r15 : n9) (r16 : n9) (r17 : n9) (r18 : n9) (r19 : n9)
       (r21 : n9) (r22 : n9) (r23 : n9) (r24 : n9) (r25 : n9) (r26 : n9) (r27 : n9) (r28 : n9) (r29 : n9)
       (r31 : n9) (r32 : n9) (r33 : n9) (r34 : n9) (r35 : n9) (r36 : n9) (r37 : n9) (r38 : n9) (r39 : n9)
       (r41 : n9) (r42 : n9) (r43 : n9) (r44 : n9) (r45 : n9) (r46 : n9) (r47 : n9) (r48 : n9) (r49 : n9)
       (r51 : n9) (r52 : n9) (r53 : n9) (r54 : n9) (r55 : n9) (r56 : n9) (r57 : n9) (r58 : n9) (r59 : n9)
       (r61 : n9) (r62 : n9) (r63 : n9) (r64 : n9) (r65 : n9) (r66 : n9) (r67 : n9) (r68 : n9) (r69 : n9)
       (r71 : n9) (r72 : n9) (r73 : n9) (r74 : n9) (r75 : n9) (r76 : n9) (r77 : n9) (r78 : n9) (r79 : n9)
       (r81 : n9) (r82 : n9) (r83 : n9) (r84 : n9) (r85 : n9) (r86 : n9) (r87 : n9) (r88 : n9) (r89 : n9)
       (r91 : n9) (r92 : n9) (r93 : n9) (r94 : n9) (r95 : n9) (r96 : n9) (r97 : n9) (r98 : n9) (r99 : n9))
      (valid_9x9 r11 r12 r13 r14 r15 r16 r17 r18 r19)
      (valid_9x9 r11 r21 r31 r41 r51 r61 r71 r81 r91)
      (valid_9x9 r11 r21 r31 r12 r22 r32 r13 r23 r33)

      (valid_9x9 r21 r22 r23 r24 r25 r26 r27 r28 r29)
      (valid_9x9 r12 r22 r32 r42 r52 r62 r72 r82 r92)
      (valid_9x9 r14 r15 r16 r24 r25 r26 r34 r35 r36)

      (valid_9x9 r31 r32 r33 r34 r35 r36 r37 r38 r39)
      (valid_9x9 r13 r23 r33 r43 r53 r63 r73 r83 r93)
      (valid_9x9 r17 r18 r19 r27 r28 r29 r37 r38 r39)

      (valid_9x9 r41 r42 r43 r44 r45 r46 r47 r48 r49)
      (valid_9x9 r14 r24 r34 r44 r54 r64 r74 r84 r94)
      (valid_9x9 r41 r42 r43 r51 r52 r53 r61 r62 r63)

      (valid_9x9 r51 r52 r53 r54 r55 r56 r57 r58 r59)
      (valid_9x9 r15 r25 r35 r45 r55 r65 r75 r85 r95)
      (valid_9x9 r44 r45 r46 r54 r55 r56 r64 r65 r66)

      (valid_9x9 r61 r62 r63 r64 r65 r66 r67 r68 r69)
      (valid_9x9 r16 r26 r36 r46 r56 r66 r76 r86 r96)
      (valid_9x9 r47 r48 r49 r57 r58 r59 r67 r68 r69)

      (valid_9x9 r71 r72 r73 r74 r75 r76 r77 r78 r79)
      (valid_9x9 r17 r27 r37 r47 r57 r67 r77 r87 r97)
      (valid_9x9 r71 r72 r73 r81 r82 r83 r91 r92 r93)

      (valid_9x9 r81 r82 r83 r84 r85 r86 r87 r88 r89)
      (valid_9x9 r18 r28 r38 r48 r58 r68 r78 r88 r98)
      (valid_9x9 r74 r75 r76 r84 r85 r86 r94 r95 r96)

      (valid_9x9 r91 r92 r93 r94 r95 r96 r97 r98 r99)
      (valid_9x9 r19 r29 r39 r49 r59 r69 r79 r89 r99)
      (valid_9x9 r77 r78 r79 r87 r88 r89 r97 r98 r99)
      )

    ;;; Running a goal
    (run 1
       ((r11 : n9) (r12 : n9) (r13 : n9)                       (r16 : n9) (r17 : n9)            (r19 : n9)
                   (r22 : n9) (r23 : n9)            (r25 : n9) (r26 : n9) (r27 : n9) (r28 : n9) (r29 : n9)
        (r31 : n9)            (r33 : n9) (r34 : n9) (r35 : n9)                       (r38 : n9) (r39 : n9)
        (r41 : n9) (r42 : n9)            (r44 : n9)            (r46 : n9) (r47 : n9)
                   (r52 : n9) (r53 : n9)            (r55 : n9)            (r57 : n9) (r58 : n9)
                              (r63 : n9) (r64 : n9)            (r66 : n9)            (r68 : n9) (r69 : n9)
        (r71 : n9) (r72 : n9)                       (r75 : n9) (r76 : n9) (r77 : n9)            (r79 : n9)
                   (r82 : n9) (r83 : n9) (r84 : n9) (r85 : n9)            (r87 : n9) (r88 : n9)
        (r91 : n9) (r92 : n9) (r93 : n9) (r94 : n9)                       (r97 : n9) (r98 : n9) (r99 : n9))
      (sudoku_9x9
       r11 r12 r13 8   0   r16 r17 5   r19
       3   r22 r23 2   r25 r26 r27 r28 r29
       r31 4   r33 r34 r35 6   0   r38 r39
       r41 r42 3   r44 7   r46 r47 8   4
       4   r52 r53 1   r55 3   r57 r58 7
       7   1   r63 r64 8   r66 5   r68 r69
       r71 r72 0   4   r75 r76 r77 1   r79
       8   r82 r83 r84 r85 0   r87 r88 5
       r91 r92 r93 r94 5   1   r97 r98 r99))))
