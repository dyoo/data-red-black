#lang setup/infotab
(define name "data/red-black: red-black trees")
(define categories '(datastructures))
(define can-be-loaded-with 'all)
(define required-core-version "5.3.1")
(define version "1.0")
(define repositories '("4.x"))
(define scribblings '(("data-red-black.scrbl")))
(define blurb '("General red-black trees.  Includes an implementation
of augmented red-black trees, where each node has metadata, as well as
a specialized version for representing string trees with
search-by-position."))
(define release-notes '((p "First release.")))
(define deps (list))
