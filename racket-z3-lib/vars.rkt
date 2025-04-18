#lang racket
(require "./ffi/enums.rkt"
         "./ffi/functions.rkt"
         "./ffi/types.rkt")

(define (mk-var ctx name sort)
  (define sym  (Z3_mk_string_symbol ctx (string->bytes/utf-8 name)))
  (Z3_mk_const ctx sym sort))

(define (mk-bool-var   ctx n) (mk-var ctx n (Z3_mk_bool_sort   ctx)))
(define (mk-int-var    ctx n) (mk-var ctx n (Z3_mk_int_sort    ctx)))
(define (mk-real-var   ctx n) (mk-var ctx n (Z3_mk_real_sort   ctx)))
(define (mk-string-var ctx n) (mk-var ctx n (Z3_mk_string_sort ctx)))

(define (mk-int ctx v)
  (Z3_mk_int ctx v (Z3_mk_int_sort ctx)))

(provide (all-defined-out))
