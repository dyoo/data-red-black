#lang racket/base

;; Implementation of an augmented red-black trees; extra information supports
;; position-based queries, as used in tokenization.
;;
;; The elements in the tree are intended to be tokens with a particular width;
;; we wish to make it easy to represent a sequence of tokens, and also
;; insert at the front and back.
;;
;; We follow the basic outline for order-statistic trees described in CLRS.
;; In our case, each node remembers the total width of the subtree.  This allows
;; us to perform position queries in time proportional to the tree height.
;;

(require profile)


(define red 'red)
(define black 'black)

(struct tree (root)  ;; node
  #:mutable
  #:transparent)

(struct node (data          ;; Any
              self-width    ;; Natural
              subtree-width ;; Natural
              parent     ;; (U Node null)
              left       ;; (U Node null)
              right      ;; (U Node null)
              color)     ;; (U red black)
  #:mutable
  #:transparent)




;; left-rotate!: tree node -> void
;; Rotates the x node node to the left.
;; Preserves the auxiliary information for position queries.
(define (left-rotate! a-tree x)  
  (define y (node-right x))
  (set-node-right! x (node-left y))
  (unless (eq? (node-left y) null)
    (set-node-parent! (node-left y) x))
  (set-node-parent! y (node-parent x))
  (cond [(eq? (node-parent x) null)
         (set-tree-root! a-tree y)]
        [(eq? x (node-left (node-parent x)))
         (set-node-left! (node-parent x) y)]
        [else
         (set-node-right! (node-parent x) y)])
  (set-node-left! y x)
  (set-node-parent! x y)
  (update-width-to-root! x))


;; right-rotate!: tree node -> void
;; Rotates the y node node to the right.  (Symmetric to the left-rotate! function.)
;; Preserves the auxiliary information for position queries.
(define (right-rotate! a-tree y)
  (define x (node-left y))
  (set-node-left! y (node-right x))
  (unless (eq? (node-right x) null)
    (set-node-parent! (node-right x) y))
  (set-node-parent! x (node-parent y))
  (cond [(eq? (node-parent y) null)
         (set-tree-root! a-tree x)]
        [(eq? y (node-right (node-parent y)))
         (set-node-right! (node-parent y) x)]
        [else
         (set-node-left! (node-parent y) x)])
  (set-node-right! x y)
  (set-node-parent! y x)
  (update-width-to-root! y))



;; insert-back!: tree data width -> void
;; Insert at the back of the tree.
(define (insert-back! a-tree data width)
  (define x (node data width width null null null red))
  (cond
    [(eq? (tree-root a-tree) null)
     (set-tree-root! a-tree x)]
    [else
     (let loop ([p (tree-root a-tree)])
       (let ([r (node-right p)])
         (cond
           [(eq? r null)
            (set-node-right! p x)
            (set-node-parent! x p)]
           [else
            (loop r)])))])
  (update-width-to-root! x)
  (fix/insert! a-tree x))


;; insert-front!: tree dat width -> void
;; Insert at the front of the tree.
(define (insert-front! a-tree data width)
  (define x (node data width width null null null red))
  (cond
    [(eq? (tree-root a-tree) null)
     (set-tree-root! a-tree x)]
    [else
     (let loop ([p (tree-root a-tree)])
       (let ([l (node-left p)])
         (cond
           [(eq? l null)
            (set-node-left! p x)
            (set-node-parent! x p)]
           [else
            (loop l)])))])
  (update-width-to-root! x)
  (fix/insert! a-tree x))


(define (update-width-to-root! a-node)
  (cond
    [(null? a-node)
     (void)]
    [else
     (define left (node-left a-node))
     (define right (node-right a-node))
     (set-node-subtree-width! a-node
                              (+ (if (eq? null left) 
                                     0
                                     (node-subtree-width left))
                                 (if (eq? null right) 
                                     0
                                     (node-subtree-width right))
                                 (node-self-width a-node)))
     (update-width-to-root! (node-parent a-node))]))


;; new-tree: -> tree
(define (new-tree)
  (tree null))


;; Corrects the red/black tree property via node rotations after an insertion.
;; fix/insert!: node 
(define (fix/insert! a-tree z)
  (let loop ([z z])
    (define z.p (node-parent z))
    (when (and (not (eq? z.p null))
               (eq? (node-color z.p) red))
      (define z.p.p (node-parent z.p))
      (cond [(eq? z.p (node-left z.p.p))
             (define y (node-right z.p.p))
             (cond [(and (not (eq? y null))
                         (eq? (node-color y) red))
                    (set-node-color! z.p black)
                    (set-node-color! y black)
                    (set-node-color! z.p.p red)
                    (loop z.p.p)]
                   [else
                    (cond [(eq? z (node-right z.p))
                           (let ([new-z z.p])
                             (left-rotate! a-tree new-z)
                             (set-node-color! (node-parent new-z) black)
                             (set-node-color! (node-parent (node-parent new-z)) red)
                             (right-rotate! a-tree (node-parent (node-parent new-z)))
                             (loop new-z))]
                          [else
                           (set-node-color! z.p black)
                           (set-node-color! z.p.p red)
                           (right-rotate! a-tree z.p.p)
                           (loop z)])])]
            [else
             (define y (node-left z.p.p))
             (cond [(and (not (eq? y null))
                         (eq? (node-color y) red))
                    (set-node-color! z.p black)
                    (set-node-color! y black)
                    (set-node-color! z.p.p red)
                    (loop z.p.p)]
                   [else
                    (cond [(eq? z (node-left z.p))
                           (let ([new-z z.p])
                             (right-rotate! a-tree new-z)
                             (set-node-color! (node-parent new-z) black)
                             (set-node-color! (node-parent (node-parent new-z)) red)
                             (left-rotate! a-tree (node-parent (node-parent new-z)))
                             (loop new-z))]
                          [else
                           (set-node-color! z.p black)
                           (set-node-color! z.p.p red)
                           (left-rotate! a-tree z.p.p)
                           (loop z)])])])))
  (set-node-color! (tree-root a-tree) black))



(define (tree-items a-tree)
  (let loop ([node (tree-root a-tree)]
             [acc null])
    (cond
      [(null? node)
       acc]
      [else
       (loop (node-left node)
             (cons (list (node-data node)
                         (node-self-width node))
                   (loop (node-right node) acc)))])))


;; tree-height: tree -> natural
(define (tree-height a-tree)
  (let loop ([node (tree-root a-tree)])
    (cond
      [(null? node)
       0]
      [else
       (+ 1 (max (loop (node-left node))
                 (loop (node-right node))))])))


(module+ test
  (require rackunit racket/block)
  
  
  ;; tree->list: tree -> list
  ;; For debugging: help visualize what the structure of the tree looks like.
  (define (tree->list a-tree)
    (let loop ([node (tree-root a-tree)])
      (cond
        [(null? node)
         null]
        [else
         (list (format "~a:~a" 
                       (node-data node)
                       (node-color node))
               (loop (node-left node))
               (loop (node-right node)))])))
  
  
  ;; checking rotations
  (block 
   (define t (new-tree))
   
   (define alpha (node "alpha" 5 5 null null null null))
   (define beta (node "beta" 4 5 null null null null))
   (define gamma (node "gamma" 5 5 null null null null))
   
   (define x (node "x" 1 1 null alpha beta null))
   (define y (node "y" 1 1 null null gamma null))
   (set-tree-root! t y)
   (set-node-left! y x)
   (set-node-parent! x y)
   
   (right-rotate! t y)
   (check-eq? (tree-root t) x)
   (check-eq? (node-left (tree-root t)) alpha)
   (check-eq? (node-right (tree-root t)) y)
   (check-eq? (node-left (node-right (tree-root t))) beta)
   (check-eq? (node-right (node-right (tree-root t))) gamma)
   
   (left-rotate! t x)
   (check-eq? (tree-root t) y)
   (check-eq? (node-right (tree-root t)) gamma)
   (check-eq? (node-left (tree-root t)) x)
   (check-eq? (node-left (node-left (tree-root t))) alpha)
   (check-eq? (node-right (node-left (tree-root t))) beta))
  
  
  
  (block (define t (new-tree))
         (insert-back! t "foobar" 6)
         (insert-back! t "hello" 5)
         (insert-back! t "world" 5)
         (check-equal? (tree-items t)
                       '(("foobar" 6)
                         ("hello" 5)
                         ("world" 5))))
  
  
  (block (define t (new-tree))
         (insert-front! t "a" 1)
         (insert-front! t "b" 1)
         (insert-front! t "c" 1)
         (check-equal? (tree-items t)
                       '(("c" 1) ("b" 1) ("a" 1)))
         (check-equal? (tree->list t)
                       '("b:black" ("c:red" () ()) ("a:red" () ()))))
  
  (block (define t (new-tree))
         (insert-front! t "alpha" 5)
         (insert-front! t "beta" 4)
         (insert-front! t "gamma" 5)
         (insert-front! t "delta" 5)
         (insert-front! t "omega" 5)
         (check-equal? (tree-items t)
                       '(("omega" 5)("delta" 5)("gamma" 5) ("beta" 4) ("alpha" 5))))
  
  
  
  (block (define t (new-tree))
         (insert-back! t "hi" 2)
         (insert-back! t "bye" 3)
         (define the-root (tree-root t))
         (check-equal? (node-left the-root)
                       null)
         (check-equal? (node-color the-root)
                       black)
         (check-equal? (node-subtree-width the-root) 5)
         (check-equal? (node-color (node-right the-root))
                       red))
  
  (block (define t (new-tree))
         (insert-back! t "hi" 2)
         (insert-back! t "bye" 3)
         (insert-back! t "again" 5)
         (define the-root (tree-root t))
         (check-equal? (node-data (node-left the-root))
                       "hi")
         (check-equal? (node-data the-root)
                       "bye")
         (check-equal? (node-data (node-right the-root))
                       "again")
         (check-equal? (node-color the-root)
                       black)
         (check-equal? (node-color (node-left the-root)) red)
         (check-equal? (node-color (node-right the-root)) red)
         (check-equal? (node-subtree-width the-root) 10))
  
  
  
  (when (file-exists? "/usr/share/dict/words")
    (printf "Timing construction of /usr/share/dict/words:\n")
    (define t (new-tree))
    (define all-words (call-with-input-file "/usr/share/dict/words" 
                        (lambda (ip) (for/list ([line (in-lines ip)]) line))))
    (profile
     #:delay 0.00001
     (for ([word (in-list all-words)]
           [i (in-naturals)])
       #;(when (= 1 (modulo i 1000))
           (printf "loaded ~s words; tree height=~s\n" i (tree-height t)))
       (insert-back! t word (string-length word))))
    
    (profile
     #:delay 0.00001
     (for ([word (in-list all-words)]
           [i (in-naturals)])
       #;(when (= 1 (modulo i 1000))
           (printf "loaded ~s words; tree height=~s\n" i (tree-height t)))
       (insert-front! t word (string-length word))))))
