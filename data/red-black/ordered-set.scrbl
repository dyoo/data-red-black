#lang scribble/manual
@(require scribble/manual
          scribble/eval
          (for-label data/red-black/ordered-set
                     racket/base
                     racket/set
                     racket/string))

@(define my-eval (make-base-eval))
@(my-eval '(require data/red-black/ordered-set racket/string racket/set))


@title{Ordered sets: mutable sets with a total order}
@author+email["Danny Yoo" "dyoo@hashcollision.org"]


@defmodule[data/red-black/ordered-set]

This module provides a mutable, set-like container of totally-ordered elements.

As a quick example:

@interaction[#:eval my-eval
(require data/red-black/ordered-set)
(define s1 (ordered-set))
(for ([w (string-split 
          (string-append "this is a test of the emergency broadcast"
                         " system this is only a test"))])
  (ordered-set-add! s1 w))
@code:comment{Let's query for membership:}
(ordered-set-member? s1 "broadcast")
(ordered-set-member? s1 "radio")
@code:comment{The ordered set acts as a sequence:}
(for/list ([w s1]) w)
(ordered-set-remove! s1 "broadcast")
(ordered-set-member? s1 "broadcast")
]


For convenience, these ordered sets use the notion of the total-order defined
by the @racket[datum-order] function in @racketmodname[data/order].  The
@racket[ordered-set] constructor can take an optional @racket[#:order]
comparision function to customize how its elements compare.

But be careful about defining your own ordering function.  The following
example shows where it might go wrong:

@interaction[#:eval my-eval
@code:comment{order-strings-by-length: string string -> (or/c '< '= '>)}
(define (order-strings-by-length x y)
  (define xs (string-length x))
  (define ys (string-length y))
  (cond [(< xs ys) '<]
        [(= xs ys) '=] @code:comment{ (probably buggy.  See below...)}
        [(> xs ys) '>]))
(define a-set (ordered-set #:order order-strings-by-length))
(for ([word (string-split "we few we happy few we band of brothers")])
  (ordered-set-add! a-set word))
@code:comment{Note that we know that "of" will be missing from the list!}
@code:comment{That's because the comparison function makes "of" and "we"}
@code:comment{look the same:}
(ordered-set->list a-set)
]

The ordered set trusts the order provided by @racket[#:order] for all
comparisons, including equality.  In the example above, @racket["of"] and
@racket["we"] compare the same, and @racket[ordered-set-add!]  ignores
operations that insert a value that already exists in the set.


On the implementation side: an ordered set hold onto its elements with a
red-black tree, so that most operations work in time logarithmic to the set's
@racket[ordered-set-count].


@section[#:tag "ordered-set-api"]{API}

@defproc[(ordered-set [#:order order 
                                    (any/c any/c . -> . (or/c '< '= '>))
                                    datum-order]
                          [initial-elt any/c] ...)
         ordered-set/c]{
Constructs a new ordered set.
@interaction[#:eval my-eval
(define my-set (ordered-set))
my-set
(for/list ([x my-set]) x)
@code:comment{Creating an ordered set with initial elements:}
(define another-set (ordered-set 3 1 4 1 5 9))
(for/list ([x another-set]) x)
]


By default, this uses @racket[datum-order]
to compare its elements; this default can be overridden by providing
an @racket[#:order] that can compare two elements:
@interaction[#:eval my-eval
@code:comment{Overriding #:order for descending sort:}
(define (cmp x y)
  (cond [(< x y) '>]
        [(= x y) '=]
        [(> x y) '<]))
(define yet-another-set (ordered-set #:order cmp
                                     3 1 4 1 5 9))
(for/list ([x yet-another-set]) x)]
}


@defproc[(ordered-set? [x any/c]) boolean?]{
Returns true if @racket[x] is an ordered set.
@interaction[#:eval my-eval
(ordered-set? (ordered-set))
(ordered-set? (list 1 2 3))
@code:comment{The built in sets in Racket's racket/set library}
@code:comment{are not ordered sets:}
(ordered-set? (set))]
}


@defthing[ordered-set/c flat-contract?]{
A flat contract for ordered sets.
}


@defproc[(ordered-set-order [a-set ordered-set/c]) (any/c any/c . -> . (or/c '< '= '>))]{
Returns the total-ordering function used by ordered set @racket[a-set].
@interaction[#:eval my-eval
(define f (ordered-set-order (ordered-set)))
(f 3 4)
(f 4 4)
(f 4 3)]
}


@defproc[(ordered-set-empty? [a-set ordered-set/c]) boolean?]{
Returns true if the ordered set @racket[a-set] is empty.
@interaction[#:eval my-eval
(ordered-set-empty? (ordered-set))
(ordered-set-empty? (ordered-set 'nonempty "set!"))]
}


@defproc[(ordered-set-count [a-set ordered-set/c]) natural-number/c]{
Returns the number of elements in the ordered set @racket[a-set].
@interaction[#:eval my-eval
(ordered-set-count (ordered-set "duck" "duck" "goose"))
]
}


@defproc[(ordered-set-member? [a-set ordered-set/c] [x any/c]) boolean?]{
Returns true if @racket[x] is an element in ordered set @racket[a-set].
@interaction[#:eval my-eval
(define keywords (ordered-set "lambda" "case" "cond" "define"))
(ordered-set-member? keywords "guitar")
@; ... gently weeps
(ordered-set-member? keywords "lambda")]
}


@defproc[(ordered-set-add! [a-set ordered-set/c] [x any/c]) void?]{
Adds @racket[x] into ordered set @racket[a-set].  If @racket[x] is already
an element, this has no effect.
@interaction[#:eval my-eval
(define a-set (ordered-set))
(ordered-set-add! a-set "racket")
(ordered-set-add! a-set "prolog")
(ordered-set-add! a-set "java")
(ordered-set-add! a-set "ocaml")
(for/list ([x a-set]) x)
]

Be aware that this operation depends on the correctness of the total-ordering
function of @racket[a-set].  If the order doesn't distinguish between
unequal elements, unexpected results may follow:
@interaction[#:eval my-eval
(define (bad-cmp x y) '=)
(define a-weird-set (ordered-set #:order bad-cmp))
(ordered-set-add! a-weird-set "racket")
(ordered-set-add! a-weird-set "prolog")
(ordered-set-add! a-weird-set "java")
(ordered-set-add! a-weird-set "ocaml")
(for/list ([x a-weird-set]) x)
]
}


@defproc[(ordered-set-remove! [a-set ordered-set/c] [x any/c]) void?]{
Removes @racket[x] from ordered set @racket[a-set].  If @racket[x] is not
an element of @racket[a-set], this has no effect.
@interaction[#:eval my-eval
(define leagues (ordered-set "gold" "silver" "bronze" "tin" "wood"))
(ordered-set-member? leagues "tin")
(ordered-set-remove! leagues "tin")
(ordered-set-member? leagues "tin")
]

Just as with @racket[ordered-set-add!],  @racket[ordered-set-remove!]'s
behavior depends on the correctness of the set's total ordering function.
}



@defproc[(ordered-set->list [a-set ordered-set/c]) list?]{
Returns the elements of ordered set @racket[a-set] as a list, where
the elements are sorted according to @racket[a-set]'s total-order.
@interaction[#:eval my-eval
(define cloud-types (ordered-set "cumulus" "stratus" "cirrus" "nimbus"))
(ordered-set->list cloud-types)
]
}



@defproc[(in-ordered-set [a-set ordered-set/c]) sequence?]{

Explicitly constructs a sequence of the elements in ordered set @racket[a-set].

@interaction[#:eval my-eval
(define a-sequence (in-ordered-set (ordered-set "a" "b" "b" "a")))
a-sequence
(for ([x a-sequence]) (printf "I see: ~a\n" x))
]

Note that ordered sets are already treated implicitly as sequences.
@interaction[#:eval my-eval
(for ([x (ordered-set "a" "b" "b" "a")]) (printf "I see: ~a\n" x))]
}


@close-eval[my-eval]