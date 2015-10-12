;; This buffer is for notes you don't want to save, and for Lisp evaluation.
;; If you want to create a file, visit that file with C-x C-f,
;; then enter the text in that file's own buffer.

a : ('a => 'b => 'a)
    => 'a 
    => 'b list
    => 'b list
    => 'b 
    => 'b list
    => 'a 
    => ('a => 'b => 'a)
    => 'b list 
    => ?'a 
  = %a b c d e f g h i. g

f : ('a => 'b => 'a)
    => 'a 
    => 'b list
    => 'b list
    => 'b 
    => 'b list
    => 'a 
    => ('a => 'b => 'a)
    => 'b list
    => ?'a
    => ?'b_1.0
    => ?'a 
  = %a b c d e f g h i j k.
                 h ((%a b c d e f g h i j k. ?fa1) a b c d e f g h i j k)
                  ((%a b c d e f g h i j k. ?f1) a b c d e f g h i j k)

f1 : ('a => 'b => 'a)
    => 'a 
    => 'b list
    => 'b list
    => 'b => 'b list
    => 'a 
    => ('a => 'b => 'a)
    => 'b list
    => 'a 
    => 'b 
    => 'b 
  = %a b c d e f g h i j k. k

fa1 : ('a => 'b => 'a)
    => 'a 
    => 'b list
    => 'b list
    => 'b => 'b list
    => 'a 
    => ('a => 'b => 'a)
    => 'b list
    => 'a 
    => 'b 
    => 'a 
  = %a b c d e f g h i j k. j
