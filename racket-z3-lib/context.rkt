#lang racket
(require ffi/unsafe
         "./ffi/enums.rkt"
         "./ffi/functions.rkt"
         "./ffi/types.rkt")

(define (mk-proof-context)
  (define cfg (Z3_mk_config))
  (Z3_set_param_value cfg "proof" "true")
  (define ctx (Z3_mk_context cfg))
  (Z3_del_config cfg)
  (unless (and ctx (cpointer? ctx))
    (error 'mk-proof-context
           "Z3_mk_context returned NULL (context creation failed)"))
  ctx)

(provide (all-defined-out))
