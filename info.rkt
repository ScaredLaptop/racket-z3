#lang info
(define name "racket-z3")
(define collection "multi")
(define pkgs '("racket-z3-lib"
               "racket-z3-test"
               "racket-z3-doc"))
(define version "0.1")
(define pkg-desc "Racket bindings for the Z3 SMT solver")
(define deps '("base" "rackunit-lib"))
(define build-deps '("rackunit-lib" "scribble-lib"))