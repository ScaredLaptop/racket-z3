#lang racket
(require "./ffi/enums.rkt"
         "./ffi/functions.rkt"
         "./ffi/types.rkt")

(define (print-model ctx mdl)
  (displayln "MODEL:")
  (define num-decls (_Z3_model_get_num_consts ctx mdl))
  (for ([i (in-range num-decls)])
    (define fd  (_Z3_model_get_const_decl ctx mdl i))
    (define sym (_Z3_get_decl_name ctx fd))
    (define val (_Z3_model_get_const_interp ctx mdl fd))
    (printf "  ~a = ~a\n"
            (_Z3_get_symbol_string ctx sym)
            (_Z3_ast_to_string ctx val))))

(provide (all-defined-out))
