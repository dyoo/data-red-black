#lang racket
(require file/gunzip
         racket/runtime-path)

;; We keep a local copy of my /usr/share/dict/words file just to make
;; it easy to run these tests anywhere.

(provide all-words)
(define-runtime-path words.gz "words.gz")
(define all-words
  (delay (let ()
           (define-values (in out) (make-pipe))
           (thread (lambda () (call-with-input-file words.gz
                                (lambda (fin) 
                                  (gunzip-through-ports fin out)
                                  (close-output-port out)))))
           (for/list ([word (in-lines in)]) word))))