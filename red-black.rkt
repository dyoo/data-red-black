#lang racket/base
(require (for-syntax racket/base))

;; Implementation of an augmented red-black tree, where extra
;; information supports position-based queries.
;; 
;; The usage case of this structure is to maintain an ordered sequence
;; of items.  Each item has an internal length.  We want to support
;; quick lookup by position, as well as the catenation and splitting of sets.
;; These operations are typical of an editor's buffer, which must maintains
;; a sequence of tokens.
;;
;; We follow the basic outline for order-statistic trees described in
;; CLRS.  In our case, each node remembers the total width of the
;; subtree.  This allows us to perform search-by-position very
;; quickly.
;; 
;; We also incorporate elements of the design in:
;;     Ron Wein.  Efficient implemenation of red-black trees with
;;     split and catenate operations.  (2005)
;;     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.109.4875
;; 



;; First, our data structures:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define red 'red)
(define black 'black)


(struct tree (root  ;; (U null node)    The root node of the tree.
              first ;; (U null node)    optimization: Points to the first element.
              last  ;; (U null node)    optimization: Points to the last element.
              )
  #:mutable)

(struct node (data          ;; Any
              self-width    ;; Natural
              subtree-width ;; Natural
              parent     ;; (U Node null)
              left       ;; (U Node null)
              right      ;; (U Node null)
              color)     ;; (U red black)
  #:mutable)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Next, the operations:


;; new-tree: -> tree
;; Creates a fresh tree.
(define (new-tree)
  (tree null null null))


;; left-rotate!: tree node natural -> void
;; Rotates the x node node to the left.
;; Preserves the auxiliary information for position queries.
(define (left-rotate! a-tree x)
  (define y (node-right x))
  (set-node-right! x (node-left y))
  (unless (null? (node-left y))
    (set-node-parent! (node-left y) x))
  (set-node-parent! y (node-parent x))
  (cond [(null? (node-parent x))
         (set-tree-root! a-tree y)]
        [(eq? x (node-left (node-parent x)))
         (set-node-left! (node-parent x) y)]
        [else
         (set-node-right! (node-parent x) y)])
  (set-node-left! y x)
  (set-node-parent! x y)
  (update-statistics-up-to-root! a-tree x))


;; right-rotate!: tree node natural -> void
;; Rotates the y node node to the right.
;; (Symmetric to the left-rotate! function.)
;; Preserves the auxiliary information for position queries.
(define (right-rotate! a-tree y)
  (define x (node-left y))
  (set-node-left! y (node-right x))
  (unless (null? (node-right x))
    (set-node-parent! (node-right x) y))
  (set-node-parent! x (node-parent y))
  (cond [(null? (node-parent y))
         (set-tree-root! a-tree x)]
        [(eq? y (node-right (node-parent y)))
         (set-node-right! (node-parent y) x)]
        [else
         (set-node-left! (node-parent y) x)])
  (set-node-right! x y)
  (set-node-parent! y x)
  (update-statistics-up-to-root! a-tree y))


;; insert-last!: tree data width -> void
;; Insert after the last element in the tree.
(define (insert-last! a-tree data width)
  (define x (node data width width null null null red))
  (cond
    [(null? (tree-root a-tree))
     (set-tree-root! a-tree x)
     (set-tree-first! a-tree x)
     (set-tree-last! a-tree x)]
    [else
     (define last (tree-last a-tree))
     (set-node-right! last x)
     (set-node-parent! x last)
     (set-tree-last! a-tree x)])
  (update-statistics-up-to-root! a-tree x)
  (fix-red-red-after-insert! a-tree x))


;; insert-first!: tree dat width -> void
;; Insert before the first element of the tree.
(define (insert-first! a-tree data width)
  (define x (node data width width null null null red))
  (cond
    [(null? (tree-root a-tree))
     (set-tree-root! a-tree x)
     (set-tree-first! a-tree x)
     (set-tree-last! a-tree x)]
    [else
     (define first (tree-first a-tree))
     (set-node-left! first x)
     (set-node-parent! x first)
     (set-tree-first! a-tree x)])
  (update-statistics-up-to-root! a-tree x)
  (fix-red-red-after-insert! a-tree x))


;; update-statistics-up-to-root!: tree node natural? -> void
;; Updates a few statistics.
;;
;; 1.  The subtree width field of a-node and its ancestors should be updated.
;; 2.  The subtree-black-height should be the known black height of the immedidate
;; subtree of a-node.
(define (update-statistics-up-to-root! a-tree a-node)
  (let loop ([a-node a-node])
    (cond
      [(null? a-node)
       (void)]
      [else
       (define left (node-left a-node))
       (define right (node-right a-node))
       (set-node-subtree-width! a-node
                                (+ (if (null? left) 
                                       0
                                       (node-subtree-width left))
                                   (if (null? right) 
                                       0
                                       (node-subtree-width right))
                                   (node-self-width a-node)))
       (loop (node-parent a-node))])))


;; subtree-width: (U node null) -> natural
;; Return the subtree width of the tree rooted at n.
(define-syntax-rule (subtree-width n)
  (if (null? n)
      0
      (node-subtree-width n)))


;; search: tree natural -> (U node null)
;; Search for the node closest to offset.
;; Making the total length of the left tree at least offset, if possible.
(define (search a-tree offset)
  (let loop ([offset offset]
             [a-node (tree-root a-tree)])
    (cond
      [(null? a-node) null]
      [else
       (define left (node-left a-node))
       (define left-subtree-width (subtree-width left))
       (cond [(< offset left-subtree-width)
              (loop offset left)]
             [else 
              (define residual-offset (- offset left-subtree-width))
              (define self-width (node-self-width a-node))
              (cond
                [(< residual-offset self-width)
                 a-node]
                [else
                 (loop (- residual-offset self-width)
                       (node-right a-node))])])])))


;; fix-red-after-insert!: tree node natural -> void
;; Corrects the red/black tree property via node rotations after an
;; insertion.
(define (fix-red-red-after-insert! a-tree z)
  (let loop ([z z])
    (define z.p (node-parent z))
    (when (and (not (null? z.p))
               (eq? (node-color z.p) red))
      (define z.p.p (node-parent z.p))
      (cond [(eq? z.p (node-left z.p.p))
             (define y (node-right z.p.p))
             (cond [(and (not (null? y))
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
             (cond [(and (not (null? y))
                         (eq? (node-color y) red))
                    (set-node-color! z.p black) ; fixme: write test to verify this
                    (set-node-color! y black)   ; fixme: write test to verify this
                    (set-node-color! z.p.p red) ; fixme: write test to verify this
                    (loop z.p.p)]
                   [else
                    (cond [(eq? z (node-left z.p))
                           (let ([new-z z.p])
                             (right-rotate! a-tree new-z)
                             (set-node-color! (node-parent new-z) black) ; fixme: write test to verify this
                             (set-node-color! (node-parent (node-parent new-z)) red) ; fixme: write test to verify this
                             (left-rotate! a-tree 
                                           (node-parent (node-parent new-z)))
                             (loop new-z))]
                          [else
                           (set-node-color! z.p black)
                           (set-node-color! z.p.p red)
                           (left-rotate! a-tree z.p.p)
                           (loop z)])])])))
  (set-node-color! (tree-root a-tree) black))



;; tree-items: tree -> (listof (list X number))
;; Returns a list of all the items stored in the tree.
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






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal tests.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require rackunit 
           rackunit/text-ui
           racket/string
           "test-data/all-words.rkt")
  
  ;; tree-height: tree -> natural
  ;; For debugging: returns the height of the tree.
  (define (tree-height a-tree)
    (let loop ([node (tree-root a-tree)])
      (cond
        [(null? node)
         0]
        [else
         (+ 1 (max (loop (node-left node))
                   (loop (node-right node))))])))
  
  ;; tree-node-count: tree -> natural
  ;; Counts the nodes of the tree.
  (define (tree-node-count a-tree)
    (let loop ([node (tree-root a-tree)]
               [acc 0])
      (cond
        [(null? node)
         acc]
        [else
         (loop (node-left node) (loop (node-right node) (add1 acc)))])))
  
  
  ;; Debugging: counts the number of black nodes by manually
  ;; traversing both subtrees.
  (define (node-count-black a-node)
    (let loop ([a-node a-node]
               [acc 0])
      (cond
        [(null? a-node)
         acc]
        [else
         (define right-count (loop (node-right a-node)
                                   (+ (if (eq? black (node-color a-node)) 1 0)
                                      acc)))
         (define left-count  (loop (node-left a-node) 
                                   (+ (if (eq? black (node-color a-node)) 1 0)
                                      acc)))
         (unless (= right-count left-count)
           (error 'node-count-black))
         right-count])))
  
  
  ;; check-rb-structure!: tree -> void
  ;; The following is a heavy debugging function to ensure
  ;; tree-structure is as expected.  Note: this functions is
  ;; EXTRAORDINARILY expensive.  Do not use this outside of tests.
  (define (check-rb-structure! a-tree)
    (define (color n)
      (if (null? n) black (node-color n)))
    
    ;; No two red nodes should be adjacent:
    (let loop ([node (tree-root a-tree)])
      (cond
        [(null? node)
         (void)]
        [(eq? red (color node))
         (when (or (eq? red (color (node-left node)))
                   (eq? red (color (node-right node))))
           (error 'check-rb-structure "rb violation: two reds are adjacent"))
         (loop (node-left node))
         (loop (node-right node))]))
    
    ;; The left and right sides should be black-balanced, for all subtrees.
    (let loop ([node (tree-root a-tree)])
      (cond
        [(null? node)
         (void)]
        [else
         (unless (= (node-count-black (node-left node))
                    (node-count-black (node-right node)))
           (displayln (tree->list a-tree))
           (error 'check-rb-structure "rb violation: not black-balanced"))
         (loop (node-left node))
         (loop (node-right node))]))
    (define observed-black-height (node-count-black (tree-root a-tree)))
    ;; The observed black height should equal that of the recorded one
    #;(unless (= (tree-black-height a-tree) observed-black-height)
      (error 'check-rb-structure
             (format "rb violation: observed height ~a is not equal to recorded height ~a"
                     observed-black-height (tree-black-height a-tree))))
    
    
    ;; As should the overall height.
    (define count (tree-node-count a-tree))
    (define observed-height (tree-height a-tree))
    (define (lg n) (/ (log n) (log 2)))
    (when (> observed-height (* 2 (lg (add1 count))))
      (error 'check-rb-structure 
             (format "rb violation: height ~a beyond 2 lg(~a)=~a" 
                     observed-height (add1 count)
                     (* 2 (log (add1 count)))))))
  
  
  ;; tree->list: tree -> list
  ;; For debugging: help visualize what the structure of the tree looks like.
  (define (tree->list a-tree)
    (let loop ([node (tree-root a-tree)])
      (cond
        [(null? node)
         null]
        [else
         (list (format "~a:~a:~a" 
                       (node-data node)
                       (node-subtree-width node)
                       (node-color node))
               (loop (node-left node))
               (loop (node-right node)))])))
  
  
  
  
  (define rotation-tests
    (test-suite 
     "Checking left and right rotation" 
     (test-begin
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
      (check-eq? (node-right (node-left (tree-root t))) beta))))
  
  
  (define insertion-tests
    (test-suite
     "Insertion tests"
     (test-begin
      (define t (new-tree))
      (insert-last! t "foobar" 6)
      (insert-last! t "hello" 5)
      (insert-last! t "world" 5)
      (check-equal? (tree-items t)
                    '(("foobar" 6)
                      ("hello" 5)
                      ("world" 5)))
      (check-rb-structure! t))
     
     
     (test-begin 
      (define t (new-tree))
      (insert-first! t "a" 1)
      (insert-first! t "b" 1)
      (insert-first! t "c" 1)
      (check-equal? (tree-items t)
                    '(("c" 1) ("b" 1) ("a" 1)))
      (check-equal? (tree->list t)
                    '("b:3:black" ("c:1:red" () ()) ("a:1:red" () ())))
      (check-rb-structure! t))
     
     
     (test-begin 
      (define t (new-tree))
      (insert-first! t "alpha" 5)
      (insert-first! t "beta" 4)
      (insert-first! t "gamma" 5)
      (insert-first! t "delta" 5)
      (insert-first! t "omega" 5)
      (check-equal? (tree-items t)
                    '(("omega" 5) ("delta" 5)
                                  ("gamma" 5) ("beta" 4) ("alpha" 5)))
      (check-rb-structure! t))
     
     
     
     (test-begin 
      (define t (new-tree))
      (insert-last! t "hi" 2)
      (insert-last! t "bye" 3)
      (define the-root (tree-root t))
      (check-equal? (node-left the-root)
                    null)
      (check-equal? (node-color the-root)
                    black)
      (check-equal? (node-subtree-width the-root) 5)
      (check-equal? (node-color (node-right the-root))
                    red)
      (check-rb-structure! t))
     
     (test-begin 
      (define t (new-tree))
      (insert-last! t "hi" 2)
      (insert-last! t "bye" 3)
      (insert-last! t "again" 5)
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
      (check-equal? (node-subtree-width the-root) 10)
      (check-rb-structure! t))))
  
  
  
  (define search-tests
    (test-suite 
     "search-tests"
     (test-begin
      (define t (new-tree))
      (check-equal? (search t 0) null)
      (check-equal? (search t 129348) null))
     
     (test-begin
      (define t (new-tree))
      (insert-last! t "hello" 5)
      (check-equal? (node-data (search t 0)) "hello")
      (check-equal? (node-data (search t 1)) "hello")
      (check-equal? (node-data (search t 2)) "hello")
      (check-equal? (node-data (search t 3)) "hello")
      (check-equal? (node-data (search t 4)) "hello")
      ;; Edge case:
      (check-equal? (search t 5) null)
      ;; Edge case:
      (check-equal? (search t -1) null))
     
     
     ;; Empty nodes should get skipped over by search, though
     ;; the nodes are still there in the tree.
     (test-begin
      (define t (new-tree))
      (insert-last! t "hello" 5)
      (insert-last! t "" 0)
      (insert-last! t "" 0)
      (insert-last! t "" 0)
      (insert-last! t "world" 5)
      (insert-last! t "" 0)
      (insert-last! t "" 0)
      (insert-last! t "" 0)
      (insert-last! t "test!" 5)
      (check-equal? (tree-node-count t) 9)
      (check-equal? (node-data (search t 0)) "hello")
      (check-equal? (node-data (search t 1)) "hello")
      (check-equal? (node-data (search t 2)) "hello")
      (check-equal? (node-data (search t 3)) "hello")
      (check-equal? (node-data (search t 4)) "hello")
      (check-equal? (node-data (search t 5)) "world")
      (check-equal? (node-data (search t 6)) "world")
      (check-equal? (node-data (search t 7)) "world")
      (check-equal? (node-data (search t 8)) "world")
      (check-equal? (node-data (search t 9)) "world")
      (check-equal? (node-data (search t 10)) "test!"))
     
     
     
     
     (test-begin
      (define t (new-tree))
      (define words (string-split "This is a test of the emergency broadcast system"))
      (for ([word (in-list words)])
        (insert-last! t word (string-length word)))
      (check-equal? (node-data (search t 0)) "This")
      (check-equal? (node-data (search t 1)) "This")
      (check-equal? (node-data (search t 2)) "This")
      (check-equal? (node-data (search t 3)) "This")
      (check-equal? (node-data (search t 4)) "is")
      (check-equal? (node-data (search t 5)) "is")
      (check-equal? (node-data (search t 6)) "a")
      (check-equal? (node-data (search t 7)) "test")
      (check-equal? (node-data (search t 8)) "test")
      (check-equal? (node-data (search t 9)) "test")
      (check-equal? (node-data (search t 10)) "test")
      (check-equal? (node-data (search t 11)) "of")
      (check-equal? (node-data (search t 12)) "of")
      (check-equal? (node-data (search t 13)) "the")
      (check-equal? (node-data (search t 14)) "the")
      (check-equal? (node-data (search t 15)) "the")
      (check-equal? (node-data (search t 16)) "emergency")
      (check-equal? (node-data (search t 25)) "broadcast")
      (check-equal? (node-data (search t 34)) "system"))))
  
  
  
  (define dict-words-tests
    (test-suite
     "Working with a lot of words.  Insert and search tests."
     (test-begin
      (define t (new-tree))
      
      (for ([word (in-list all-words)])
        (insert-last! t word (string-length word)))
      
      (check-rb-structure! t)
      
      (for/fold ([offset 0]) ([word (in-list all-words)])
        (check-equal? (node-data (search t offset)) word)
        (+ offset (string-length word))))
      
     
     ;; Do it backwards
     (test-begin
      (define t (new-tree))
      (for ([word (in-list (reverse all-words))])
        (insert-first! t word (string-length word)))
      
      (check-rb-structure! t)
      
      (for/fold ([offset 0]) ([word (in-list all-words)])
        (check-equal? (node-data (search t offset)) word)
        (+ offset (string-length word)))
      (void))))
  
  
  
  ;; Stress test
  (define exhaustive-structure-test
    (test-suite
     "Check intermediate results for tree structure"
     (test-begin
      (printf "Timing construction of /usr/share/dict/words:\n")
      (define t (new-tree))
      (collect-garbage)
      (time
       (for ([word (in-list all-words)]
             [i (in-naturals)])
         (when (= 1 (modulo i 10000))
           (printf "loaded ~s words; tree height=~s\n" i (tree-height t))
           (check-rb-structure! t))
         (insert-last! t word (string-length word))))
      ;; Be aware that the GC may make the following with insert-front! might make
      ;; it look like the first time we build the tree, it's faster than the
      ;; second time around.
      ;; The explicit calls to collect-garbage here are just to eliminate that effect.
      (collect-garbage)
      (time
       (for ([word (in-list all-words)]
             [i (in-naturals)])
         (when (= 1 (modulo i 10000))
           (printf "loaded ~s words; tree height=~s\n" i (tree-height t))
           (check-rb-structure! t))
         (insert-first! t word (string-length word)))))))
  
  
  

  (define all-tests
    (if #f    ;; Fixme: is there a good way to change this at runtime using raco test?
        (test-suite "all-tests" rotation-tests insertion-tests search-tests)
        (test-suite "all-tests" rotation-tests insertion-tests search-tests
                    dict-words-tests
                    exhaustive-structure-test)))
  (void
   (run-tests all-tests)))
