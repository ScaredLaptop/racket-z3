#lang racket
;; Ideally cover all functionality in
;; https://github.com/Z3Prover/Z3/blob/master/examples/c/test_capi.c
(require rackunit
         rackunit/text-ui
         ffi/unsafe
         racket-z3-lib/print
         racket-z3-lib/context
         racket-z3-lib/vars
         "../racket-Z3-lib/ffi/enums.rkt"
         "../racket-Z3-lib/ffi/functions.rkt"
         "../racket-Z3-lib/ffi/types.rkt"
         )

(define (test-get-full-version)
  (printf "Z3 version: ~s\n" (_Z3_get_full_version))
  (check-true (string? (_Z3_get_full_version))
              "Z3_get_full_version returns a byte string"))

(define (test-solver-sat)
  (define ctx (mk-proof-context))
  (check-not-false (cpointer? ctx) "context is non-null")
  (define s   (_Z3_mk_solver ctx))
  (_Z3_solver_assert ctx s (_Z3_mk_true ctx))
  (check-equal? (_Z3_solver_check ctx s) 'Z3_L_TRUE "solver reports SAT")
  (_Z3_del_context ctx))

(define (test-unsat-core)
  (define ctx (mk-proof-context))
  (check-not-false (cpointer? ctx) "context is non-null")
  (define p   (_Z3_mk_string_symbol ctx "p"))
  (define pv  (_Z3_mk_const ctx p (_Z3_mk_bool_sort ctx)))

  (define a1  (_Z3_mk_not ctx pv)) ; ¬p
  (define a2  pv)                 ;  p
  (define s   (_Z3_mk_solver ctx))
  (_Z3_solver_assert ctx s a1)
  (_Z3_solver_assert ctx s a2)

  (check-equal? (_Z3_solver_check ctx s) 'Z3_L_FALSE "unsat core example")
  (_Z3_del_context ctx))

(module+ test
  (define smoke-suite
    (test-suite
     "Z3-RackUnit smoke tests"
     (test-case "full version"     (test-get-full-version))
     (test-case "simple SAT"       (test-solver-sat))
     (test-case "unsat core demo"  (test-unsat-core))))
  (run-tests smoke-suite 'verbose))