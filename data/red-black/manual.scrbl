#lang scribble/manual

@title{data-red-black: augmented red black tree structures}

The @tt{data/red-black} library consists of several
red-black tree data structures.  Its contents include two red-black
tree implementations:
@itemize[

@item{@racketmodname[data/red-black/positional]: meant to support position-based queries}

@item{@racketmodname[data/red-black/augmented]: meant to support flexible node extensions}
]

as well as an application of augmented red-black trees to support an ordered set collection in @racketmodname[data/red-black/ordered-set].



@include-section["positional.scrbl"]
@include-section["augmented.scrbl"]
@include-section["ordered-set.scrbl"]
@include-section["biblio.scrbl"]