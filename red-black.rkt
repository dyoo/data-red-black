#lang racket/base
(require (for-syntax racket/base))

;; Implementation of an augmented red-black tree, where extra
;; information supports position-based queries.
;; 
;; The usage case of this structure is to maintain an ordered sequence
;; of items.  Each item has an internal length.  We want to support
;; quick lookup by position, as well as the catenation and splitting of sets.
;;
;; These operations are typical of an editor's buffer, which must maintain
;; a sequence of tokens in order, allowing for arbitrary search, insert, and delete
;; into the sequence.
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


(provide tree?
         tree-root
         node?
         nil?
         node-data
         node-self-width
         node-subtree-width
         node-parent
         node-left
         node-right
         node-color
         
         new-tree
         insert-first!
         insert-last!
         delete!
         search)

;; First, our data structures:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define red 'red)
(define black 'black)


(struct tree (root  ;; node    The root node of the tree.
              first ;; node    optimization: Points to the first element.
              last) ;; node    optimization: Points to the last element.
  #:mutable)


(struct node (data          ;; Any
              self-width    ;; Natural
              subtree-width ;; Natural
              parent     ;; node
              left       ;; node
              right      ;; node
              color)     ;; (U red black)
  #:mutable)


;; As in CLRS, we use a single nil sentinel node that represents nil.
(define nil (let ([v (node #f 0 0 #f #f #f black)])
              (set-node-parent! v v)
              (set-node-left! v v)
              (set-node-right! v v)
              v))
(define-syntax-rule (nil? x) (eq? x nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Next, the operations:


;; new-tree: -> tree
;; Creates a fresh tree.
(define (new-tree)
  (tree nil nil nil))


;; minimum: node -> node
;; Looks for the minimum element of the tree rooted at n.
(define (minimum n)
  (let loop ([n n])
    (define left (node-left n))
    (cond
      [(nil? left)
       n]
      [else
       (loop left)])))

;; maximum: node -> node
;; Looks for the maximum element of the tree rooted at n.
(define (maximum n)
  (let loop ([n n])
    (define right (node-right n))
    (cond
      [(nil? right)
       n]
      [else
       (loop right)])))


;; successor: node -> node
;; Given a node, walks to the successor node.
(define (successor x)
  (cond [(not (nil? (node-right x)))
         (minimum (node-right x))]
        [else
         (let loop ([x x]
                    [y (node-parent x)])
           (cond
             [(and (not (nil? y)) (eq? x (node-right y)))
              (loop y (node-parent y))]
             [else
              y]))]))

;; predecessor: node -> node
;; Given a node, walks to the predecessor node.
(define (predecessor x)
  (cond [(not (nil? (node-left x)))
         (maximum (node-left x))]
        [else
         (let loop ([x x]
                    [y (node-parent x)])
           (cond
             [(and (not (nil? y)) (eq? x (node-left y)))
              (loop y (node-parent y))]
             [else
              y]))]))


;; computed-node-subtree-width: node -> number
;; Assuming the node-subtree-width of the left and right are
;; correct, computes the subtree-width of n.
;; Note: this does not trust the local cache in (node-subtree-width n).
(define-syntax-rule (computed-node-subtree-width n)
  (let ([left (node-left n)]
        [right (node-right n)])
    (+ (if (nil? left)
           0 
           (node-subtree-width left))
       (node-self-width n)
       (if (nil? right)
           0 
           (node-subtree-width right)))))


;; left-rotate!: tree node natural -> void
;; INTERNAL
;; Rotates the x node node to the left.
;; Preserves the auxiliary information for position queries.
(define (left-rotate! a-tree x)
  (define y (node-right x))
  (set-node-right! x (node-left y))
  (unless (nil? (node-left y))
    (set-node-parent! (node-left y) x))
  (set-node-parent! y (node-parent x))
  (cond [(nil? (node-parent x))
         (set-tree-root! a-tree y)]
        [(eq? x (node-left (node-parent x)))
         (set-node-left! (node-parent x) y)]
        [else
         (set-node-right! (node-parent x) y)])
  (set-node-left! y x)
  (set-node-parent! x y)
  
  ;; Looking at Figure 1.32 of CLRS:
  ;; The change to the statistics can be locally computed after the
  ;; rotation:
  (set-node-subtree-width! y (node-subtree-width x))
  (set-node-subtree-width! x (computed-node-subtree-width x)))


;; right-rotate!: tree node natural -> void
;; INTERNAL
;; Rotates the y node node to the right.
;; (Symmetric to the left-rotate! function.)
;; Preserves the auxiliary information for position queries.
(define (right-rotate! a-tree y)
  (define x (node-left y))
  (set-node-left! y (node-right x))
  (unless (nil? (node-right x))
    (set-node-parent! (node-right x) y))
  (set-node-parent! x (node-parent y))
  (cond [(nil? (node-parent y))
         (set-tree-root! a-tree x)]
        [(eq? y (node-right (node-parent y)))
         (set-node-right! (node-parent y) x)]
        [else
         (set-node-left! (node-parent y) x)])
  (set-node-right! x y)
  (set-node-parent! y x)
  
  ;; Looking at Figure 1.32 of CLRS:
  ;; The change to the statistics can be locally computed after the
  ;; rotation:
  (set-node-subtree-width! x (node-subtree-width y))
  (set-node-subtree-width! y (computed-node-subtree-width y)))


;; insert-last!: tree data width -> void
;; Insert after the last element in the tree.
(define (insert-last! a-tree data width)
  (define x (node data width width nil nil nil red))
  (cond
    [(nil? (tree-root a-tree))
     (set-tree-root! a-tree x)
     (set-tree-first! a-tree x)
     (set-tree-last! a-tree x)]
    [else
     (define last (tree-last a-tree))
     (set-node-right! last x)
     (set-node-parent! x last)
     (set-tree-last! a-tree x)])
  (update-statistics-up-to-root! a-tree x)
  (fix-after-insert! a-tree x))


;; insert-first!: tree dat width -> void
;; Insert before the first element of the tree.
(define (insert-first! a-tree data width)
  (define x (node data width width nil nil nil red))
  (cond
    [(nil? (tree-root a-tree))
     (set-tree-root! a-tree x)
     (set-tree-first! a-tree x)
     (set-tree-last! a-tree x)]
    [else
     (define first (tree-first a-tree))
     (set-node-left! first x)
     (set-node-parent! x first)
     (set-tree-first! a-tree x)])
  (update-statistics-up-to-root! a-tree x)
  (fix-after-insert! a-tree x))


;; fix-after-insert!: tree node natural -> void
;; INTERNAL
;; Corrects the red/black tree property via node rotations after an
;; insertion.  If there's a violation, then it's at z where both z and
;; its parent are red.
(define (fix-after-insert! a-tree z)
  (let loop ([z z])
    (define z.p (node-parent z))
    (when (and (not (nil? z.p))
               (eq? (node-color z.p) red))
      (define z.p.p (node-parent z.p))
      (cond [(eq? z.p (node-left z.p.p))
             (define y (node-right z.p.p))
             (cond [(and (not (nil? y))
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
             (cond [(and (not (nil? y))
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




;; delete!: tree node -> void
;; Removes the node from the tree.
(define (delete! a-tree z)
  
  ;; First, adjust tree-first and tree-last if we end up
  ;; removing either from the tree.
  (when (eq? z (tree-first a-tree))
    (set-tree-first! a-tree (successor z)))
  (when (eq? z (tree-last a-tree))
    (set-tree-last! a-tree (predecessor z)))
  
  (define y z)
  (define y-original-color (node-color y))
  (let-values ([(x y-original-color)
                (cond
                  ;; If either the left or right child of z is nil,
                  ;; deletion is merely replacing z with its other child x.
                  ;; (Of course, we then have to repair the damage.)
                  [(nil? (node-left z))
                   (define z.p (node-parent z))
                   (define x (node-right z))
                   (transplant! a-tree z x)
                   ;; At this point, we need to repair the statistic where
                   ;; where the replacement happened, since z's been replaced with x.
                   ;; The x subtree is ok, so we need to begin the statistic repair
                   ;; at z.p.
                   (when (not (nil? z.p))
                     (update-statistics-up-to-root! a-tree z.p))
                   (values x y-original-color)]
                  
                  ;; This case is symmetric with the previous case.
                  [(nil? (node-right z))
                   (define z.p (node-parent z))
                   (define x (node-left z))
                   (transplant! a-tree z x)
                   (when (not (nil? z.p))
                     (update-statistics-up-to-root! a-tree z.p))
                   (values x y-original-color)]
                  
                  ;; The hardest case is when z has non-nil left and right.
                  ;; We take the minimum of z's right subtree and replace
                  ;; z with it.
                  [else
                   (let* ([y (minimum (node-right z))]
                          [y-original-color (node-color y)])
                     ;; At this point, y's left is nil by definition of minimum.
                     (define x (node-right y))
                     (cond
                       [(eq? (node-parent y) z)
                        ;; In CLRS, this is steps 12 and 13 of RB-DELETE.
                        ;; Be aware that x here can be nil, in which case we've now
                        ;; changed the contents of nil.
                        (set-node-parent! x y)]
                       [else
                        (transplant! a-tree y (node-right y))
                        (set-node-right! y (node-right z))
                        (set-node-parent! (node-right y) y)])
                     
                     (transplant! a-tree z y)
                     (set-node-left! y (node-left z))
                     (set-node-parent! (node-left y) y)
                     (set-node-color! y (node-color z))
                     (update-statistics-up-to-root! a-tree y)
                     (values x y-original-color))])])
    (cond [(eq? black y-original-color)
           (fix-after-delete! a-tree x)]
          [else
           (printf "not fixing\n")])))
  



;; transplant: tree node (U node nil) -> void
;; INTERNAL
;; Replaces the instance of node u in a-tree with v.
(define (transplant! a-tree u v)
  (define u.p (node-parent u))
  (cond [(nil? u.p)
         (set-tree-root! a-tree v)]
        [(eq? u (node-left u.p))
         (set-node-left! u.p v)]
        [else
         (set-node-right! u.p v)])
  (unless (nil? v)
    (set-node-parent! v u.p)))


;; fix-after-delete!: tree node -> void
(define (fix-after-delete! a-tree x)
  (printf "fixing\n")
  (let loop ([x x])
    (cond [(and (not (eq? x (tree-root a-tree)))
                (eq? (node-color x) black))
           (cond
             [(eq? x (node-left (node-parent x)))
              (displayln 1)
              (define w (node-right (node-parent x)))
              (define w-1 (cond [(eq? (node-color w) red)
                                 (displayln 4)
                                 (set-node-color! w black)
                                 (set-node-color! (node-parent x) red)
                                 (left-rotate! a-tree (node-parent x))
                                 (node-right (node-parent x))]
                                [else
                                 (displayln 5)
                                 w]))
              (cond [(and (eq? (node-color (node-left w-1)) black)
                          (eq? (node-color (node-right w-1)) black))
                     (displayln 2)
                     (set-node-color! w-1 red)
                     (loop (node-parent x))]
                    [else
                     (displayln 3)
                     (define w-2 (cond [(eq? (node-color (node-right w-1)) black)
                                        (displayln 6)
                                        (set-node-color! (node-left w-1) black)
                                        (set-node-color! w-1 red)
                                        (right-rotate! a-tree w-1)
                                        (node-right (node-parent x))]
                                       [else
                                        (displayln 7)
                                        w-1]))
                     (set-node-color! w-2 (node-color (node-parent x)))
                     (set-node-color! (node-parent x) black)
                     (set-node-color! (node-right w-2) black)
                     (left-rotate! a-tree (node-parent x))
                     (loop (tree-root a-tree))])]
             [else
              (displayln 8)
              (define w (node-left (node-parent x)))
              (define w-1 (cond [(eq? (node-color w) red)
                                 (displayln 9)
                                 (set-node-color! w black)
                                 (set-node-color! (node-parent x) red)
                                 (right-rotate! a-tree (node-parent x))
                                 (node-left (node-parent x))]
                                [else
                                 (displayln 10)
                                 w]))
              (cond [(and (eq? (node-color (node-left w-1)) black)
                          (eq? (node-color (node-right w-1)) black))
                     (displayln 11)
                     (set-node-color! w-1 red)
                     (loop (node-parent x))]
                    [else
                     (displayln 12)
                     (define w-2 (cond [(eq? (node-color (node-left w-1)) black)
                                        (displayln 13)
                                        (set-node-color! (node-right w-1) black)
                                        (set-node-color! w-1 red)
                                        (left-rotate! a-tree w-1)
                                        (node-left (node-parent x))]
                                       [else
                                        (displayln 14)
                                        w-1]))
                     (set-node-color! w-2 (node-color (node-parent x)))
                     (set-node-color! (node-parent x) black)
                     (set-node-color! (node-left w-2) black)
                     (right-rotate! a-tree (node-parent x))
                     (loop (tree-root a-tree))])])]
          [else
           (unless (nil? x)
             (set-node-color! x black))])))


;; update-statistics-up-to-root!: tree node natural? -> void
;; INTERNAL
;; Updates a few statistics.
;;
;; * The subtree width field of a-node and its ancestors should be updated.
(define (update-statistics-up-to-root! a-tree a-node)
  (let loop ([a-node a-node])
    (cond
      [(nil? a-node)
       (void)]
      [else
       (set-node-subtree-width! a-node (computed-node-subtree-width a-node))
       (loop (node-parent a-node))])))


;; subtree-width: (U node nil) -> natural
;; INTERNAL
;; Return the subtree width of the tree rooted at n.
(define-syntax-rule (subtree-width n)
  (if (nil? n)
      0
      (node-subtree-width n)))


;; search: tree natural -> (U node nil)
;; Search for the node closest to offset.
;; Making the total length of the left tree at least offset, if possible.
(define (search a-tree offset)
  (let loop ([offset offset]
             [a-node (tree-root a-tree)])
    (cond
      [(nil? a-node) nil]
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
           racket/list
           racket/class
           racket/promise
           "test-data/all-words.rkt")
  
  
  ;; tree-items: tree -> (listof (list X number))
  ;; Returns a list of all the items stored in the tree.
  (define (tree-items a-tree)
    (let loop ([node (tree-root a-tree)]
               [acc null])
      (cond
        [(nil? node)
         acc]
        [else
         (loop (node-left node)
               (cons (list (node-data node)
                           (node-self-width node))
                     (loop (node-right node) acc)))])))
  
  
  ;; tree-height: tree -> natural
  ;; For debugging: returns the height of the tree.
  (define (tree-height a-tree)
    (let loop ([node (tree-root a-tree)])
      (cond
        [(nil? node)
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
        [(nil? node)
         acc]
        [else
         (loop (node-left node) (loop (node-right node) (add1 acc)))])))
  
  
  ;; Debugging: counts the number of black nodes by manually
  ;; traversing both subtrees.
  (define (node-count-black a-node)
    (let loop ([a-node a-node]
               [acc 0])
      (cond
        [(nil? a-node)
         acc]
        [else
         (define right-count (loop (node-right a-node)
                                   (+ (if (eq? black (node-color a-node)) 1 0)
                                      acc)))
         (define left-count  (loop (node-left a-node) 
                                   (+ (if (eq? black (node-color a-node)) 1 0)
                                      acc)))
         (unless (= right-count left-count)
           (error 'node-count-black "~a vs ~a" right-count left-count))
         right-count])))
  
  
  ;; check-rb-structure!: tree -> void
  ;; The following is a heavy debugging function to ensure
  ;; tree-structure is as expected.  Note: this functions is
  ;; EXTRAORDINARILY expensive.  Do not use this outside of tests.
  (define (check-rb-structure! a-tree)
    (define (color n)
      (if (nil? n) black (node-color n)))
    
    ;; No two red nodes should be adjacent:
    (let loop ([node (tree-root a-tree)])
      (cond
        [(nil? node)
         (void)]
        [(eq? red (color node))
         (when (or (eq? red (color (node-left node)))
                   (eq? red (color (node-right node))))
           (error 'check-rb-structure "rb violation: two reds are adjacent"))
         (loop (node-left node))
         (loop (node-right node))]))
    
    
    ;; The maximum and minimum should be correct
    (unless (eq? (tree-first a-tree)
                 (if (nil? (tree-root a-tree)) nil (minimum (tree-root a-tree))))
      (error 'check-rb-structure "minimum is not first"))
    (unless (eq? (tree-last a-tree)
                 (if (nil? (tree-root a-tree)) nil (maximum (tree-root a-tree))))
      (error 'check-rb-structure "maximum is not last"))
    
    
    ;; The left and right sides should be black-balanced, for all subtrees.
    (let loop ([node (tree-root a-tree)])
      (cond
        [(nil? node)
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
    
    
    
    ;; The overall height must be less than 2 lg(n+1)
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
        [(nil? node)
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
      
      (define alpha (node "alpha" 5 5 nil nil nil nil))
      (define beta (node "beta" 4 5 nil nil nil nil))
      (define gamma (node "gamma" 5 5 nil nil nil nil))
      
      (define x (node "x" 1 1 nil alpha beta nil))
      (define y (node "y" 1 1 nil nil gamma nil))
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
                    nil)
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
  
  
  
  
  (define deletion-tests
    (test-suite
     "deletion-tests"
     (test-case
      "Deleting the last node in a tree should set us back to the nil case"
      (define t (new-tree))
      (insert-first! t "hello" 5)
      (delete! t (tree-root t))
      (check-equal? (tree-root t) nil))
     
     (test-case
      "Deleting the last node in a tree: first and last should be nil"
      (define t (new-tree))
      (insert-first! t "hello" 5)
      (delete! t (tree-root t))
      (check-equal? (tree-first t) nil)
      (check-equal? (tree-last t) nil))
     
     (test-case
      "Delete the last node in a two-node tree: basic structure"
      (define t (new-tree))
      (insert-last! t "dresden" 6)
      (insert-last! t "files" 5)
      (delete! t (node-right (tree-root t)))
      (check-equal? (node-data (tree-root t)) "dresden")
      (check-equal? (node-left (tree-root t)) nil)
      (check-equal? (node-right (tree-root t)) nil))
     
     (test-case
      "Delete the last node in a two-node tree: check the subtree-width has been updated"
      (define t (new-tree))
      (insert-last! t "dresden" 6)
      (insert-last! t "files" 5)
      (delete! t (node-right (tree-root t)))
      (check-equal? (node-subtree-width (tree-root t)) 6))
     
     (test-case
      "Delete the last node in a two-node tree: check that tree-first and tree-last are correct"
      (define t (new-tree))
      (insert-last! t "dresden" 6)
      (insert-last! t "files" 5)
      (delete! t (node-right (tree-root t)))
      (check-true (node? (tree-root t)))
      (check-equal? (tree-first t) (tree-root t))
      (check-equal? (tree-last t) (tree-root t)))))
  
  
  
  (define search-tests
    (test-suite 
     "search-tests"
     (test-begin
      (define t (new-tree))
      (check-equal? (search t 0) nil)
      (check-equal? (search t 129348) nil))
     
     (test-begin
      (define t (new-tree))
      (insert-last! t "hello" 5)
      (check-equal? (node-data (search t 0)) "hello")
      (check-equal? (node-data (search t 1)) "hello")
      (check-equal? (node-data (search t 2)) "hello")
      (check-equal? (node-data (search t 3)) "hello")
      (check-equal? (node-data (search t 4)) "hello")
      ;; Edge case:
      (check-equal? (search t 5) nil)
      ;; Edge case:
      (check-equal? (search t -1) nil))
     
     
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
      
      (for ([word (in-list (force all-words))])
        (insert-last! t word (string-length word)))
      
      (check-rb-structure! t)
      
      (for/fold ([offset 0]) ([word (in-list (force all-words))])
        (check-equal? (node-data (search t offset)) word)
        (+ offset (string-length word))))
     
     
     ;; Do it backwards
     (test-begin
      (define t (new-tree))
      (for ([word (in-list (reverse (force all-words)))])
        (insert-first! t word (string-length word)))
      
      (check-rb-structure! t)
      
      (for/fold ([offset 0]) ([word (in-list (force all-words))])
        (check-equal? (node-data (search t offset)) word)
        (+ offset (string-length word)))
      (void))))
  
  
  (define angry-monkey%
    (class object%
      (super-new)
      (define known-model '())
      (define t (new-tree))
      
      (define (random-word)
        (build-string (add1 (random 20))
                      (lambda (i) 
                        (integer->char (+ (char->integer #\a) (random 26))))))
      (define/public (get-tree) t)
      (define/public (get-model) known-model)
      
      (define/public (insert-front!)
        (define new-word (random-word))
        (printf "inserting ~s to front\n" new-word)
        (set! known-model (cons new-word known-model))
        (insert-first! t new-word (string-length new-word)))
      
      (define/public (insert-back!)
        (define new-word (random-word))
        (printf "inserting ~s to back\n" new-word)
        (set! known-model (append known-model (list new-word)))
        (insert-last! t new-word (string-length new-word)))
      
      (define/public (delete-random!)
        (when (not (empty? known-model))
             ;; Delete a random word if we can.
             (define k (random (length known-model)))
             (printf "deleting ~s\n" (list-ref known-model k))
             (define offset (for/fold ([offset 0]) ([i (in-range k)]
                                                    [word (in-list known-model)])
                              (+ offset (string-length word))))
             (set! known-model (let-values ([(a b) (split-at known-model k)])
                                 (append a (rest b))))
             (delete! t (search t offset))))
      
      (define/public (check-consistency!)
        ;; Check that the structure is consistent with our model.
        (check-equal? known-model (map first (tree-items t)))
        ;; And make sure it's still an rb-tree:
        (check-rb-structure! t))))
      
  
  (define angry-monkey-test
    (test-suite
     "Simulation of an angry monkey bashing at the tree, inserting and deleting at random."
     (test-begin
      (define iterations 1000)
      (define m (new angry-monkey%))
      (for ([i (in-range iterations)])
        (case (random 7)
          [(0 1 2)
           (send m insert-front!)]
          [(3 4 5)
           (send m insert-back!)]
          [(6)
           (send m delete-random!)])
        (send m check-consistency!))
      (printf "angry monkey is tired.\n"))))
  
  
  
  
  
  ;; Stress test
  (define exhaustive-structure-test
    (test-suite
     "Check intermediate results for tree structure"
     (test-begin
      (printf "Timing construction of /usr/share/dict/words:\n")
      (define t (new-tree))
      (collect-garbage)
      (time
       (for ([word (in-list (force all-words))]
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
       (for ([word (in-list (force all-words))]
             [i (in-naturals)])
         (when (= 1 (modulo i 10000))
           (printf "loaded ~s words; tree height=~s\n" i (tree-height t))
           (check-rb-structure! t))
         (insert-first! t word (string-length word)))))))
  
  
  
  
  (define all-tests
    (if #t    ;; Fixme: is there a good way to change this at runtime using raco test?
        (test-suite "all-tests" rotation-tests insertion-tests deletion-tests search-tests
                    angry-monkey-test)
        (test-suite "all-tests" rotation-tests insertion-tests deletion-tests search-tests
                    angry-monkey-test
                    dict-words-tests
                    exhaustive-structure-test)))
  (void
   (run-tests all-tests)))
