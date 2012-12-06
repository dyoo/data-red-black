#lang racket/base

;; An implementation of a set-like structure, backing the store with
;; a mutable red-black tree.

;; We'll want to provide many of the operations of:
;; http://docs.racket-lang.org/reference/sets.html

(require data/red-black/augmented
         data/order
         racket/contract)


(provide
 (contract-out
  [ordered-set? (any/c . -> . boolean?)]
  [new-ordered-set [() (#:order (any/c any/c . -> . ordering/c)) . ->* . ordered-set?]]
  [ordered-set-empty? (ordered-set? . -> . boolean?)]
  [ordered-set-member? (ordered-set? any/c . -> . boolean?)]
  [ordered-set-add! (ordered-set? any/c . -> . any)]
  [ordered-set-remove! (ordered-set? any/c . -> . any)]
  [ordered-set->list (ordered-set? . -> . list/c)]))


(struct ordered-set
  (tree order)
  #:property prop:sequence
  (lambda (s)
    (make-do-sequence 
     (lambda ()
       (values
        (lambda (pos)
          (node-data pos))
        (lambda (pos)
          (successor pos))
        (tree-first (ordered-set-tree s))
        (lambda (pos)
          (not (nil-node? pos)))
        #f
        #f)))))
     

;; new-ordered-set: [#:order order] -> ordered-set
(define (new-ordered-set #:order [order datum-order])
  (ordered-set (new-tree) order))


;; ordered-set-empty?: ordered-set -> boolean
(define (ordered-set-empty? s)
  (nil-node? (tree-root (ordered-set-tree s))))


;; ordered-set-member?: ordered-set X -> boolean
(define (ordered-set-member? s x)
  (define-values (n p) (search (ordered-set-tree s) (ordered-set-order s) x))
  (not (nil-node? n)))


;; ordered-set-add!: ordered-set X -> void
(define (ordered-set-add! s x)
  (define the-tree (ordered-set-tree s))
  (cond [(nil-node? (tree-root the-tree))
         (insert-first/data! the-tree x)]
        [else
         (define the-order (ordered-set-order s))
         (define-values (n p) (search the-tree the-order x))
         (cond
           [(nil-node? n)
            (case (the-order x (node-data p))
              [(<) 
               (insert-before/data! the-tree p x)]
              [else
               (insert-after/data! the-tree p x)])]
           [else
            (void)])]))


;; ordered-set-remove!: ordered-set X -> void
;; Removes x from the ordered set.
(define (ordered-set-remove! s x)
  (define the-tree (ordered-set-tree s))
  (cond [(nil-node? (tree-root the-tree))
         (void)]
        [else
         (define the-order (ordered-set-order s))
         (define-values (n p) (search the-tree the-order x))
         (cond
           [(nil-node? n)
            (void)]
           [else
            (delete! the-tree n)])]))
    

;; search: tree order X -> (values node node)
;; INTERNAL
;; Looks for the element in the set, using the order.  Returns
;; the node and its parent if we can find it.  Otherwise, returns
;; nil and the parent where we would have found the item.
(define (search the-tree the-order x)
  (let loop ([n (tree-root the-tree)]
             [p nil])
    (cond
      [(nil-node? n)
       (values n p)]
      [else
       (case (the-order x (node-data n))
         [(<)
          (loop (node-left n) n)]
         [(=)
          (values n p)]
         [(>)
          (loop (node-right n) n)])])))
         
  
;; ordered-set->list: ordered-set -> list
;; Returns a list of the ordered set items.
(define (ordered-set->list s)
  (tree-items (ordered-set-tree s)))


(module+ test
  (require rackunit rackunit/text-ui)
  
  (define tests
    (test-suite
     "ordered set tests"
     
     (test-case 
      "empty is empty"
      (check-true (ordered-set-empty? (new-ordered-set))))
     
     (test-case
      "non-empty is not empty"
      (define s (new-ordered-set))
      (ordered-set-add! s "hello")
      (check-false (ordered-set-empty? s)))
     
     (test-case
      "delete on empty"
      (define s (new-ordered-set))
      (ordered-set-remove! s "not there")
      (check-true (ordered-set-empty? s)))
     
     (test-case
      "add and remove"
      (define s (new-ordered-set))
      (ordered-set-add! s "zelda")
      (ordered-set-remove! s "zelda")
      (check-true (ordered-set-empty? s)))
     
     (test-case
      "add 2 and remove 1"
      (define s (new-ordered-set))
      (ordered-set-add! s "zelda")
      (ordered-set-add! s "link")
      (ordered-set-remove! s "zelda")
      (check-false (ordered-set-empty? s)))
     
     (test-case
      "add two"
      (define s (new-ordered-set))
      (ordered-set-add! s "hello")
      (ordered-set-add! s "world")
      (check-false (ordered-set-empty? s)))
     
     
     (test-case
      "iteration simple example"
       (define s (new-ordered-set))
       (ordered-set-add! s "hello")
       (ordered-set-add! s "world")
       (ordered-set-add! s "testing")
       (check-equal? (for/list ([x s]) x) '("hello" "testing" "world")))

     (test-case
      "to list simple example"
       (define s (new-ordered-set))
       (ordered-set-add! s "hello")
       (ordered-set-add! s "world")
       (ordered-set-add! s "testing")
       (check-equal? (ordered-set->list s) '("hello" "testing" "world")))))
  
  (run-tests tests))