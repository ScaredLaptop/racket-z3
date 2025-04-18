#lang racket
(require ffi/unsafe
         ffi/unsafe/define
         racket/system
         racket/file)

(define lib-name
  (cond [(eq? (system-type 'os) 'windows) "libz3.dll"]
        [(eq? (system-type 'os) 'macosx)  "libz3.dylib"]
        [else                             "libz3.so"]))

(define lib-path
  (let ([env (getenv "Z3_LIB_PATH")])
    (cond
      [env (build-path env lib-name)]
      [(eq? (system-type 'os) 'macosx)
       (let ([intel-path "/usr/local/lib/libz3.dylib"]
             [arm-path "/opt/homebrew/lib/libz3.dylib"])
         (cond
           [(file-exists? arm-path) arm-path]
           [(file-exists? intel-path) intel-path]
           [else lib-name]))]
      [else lib-name])))

(define lib (ffi-lib lib-path #:fail (λ () (error "Cannot load Z3 native lib" lib-path))))
(define-ffi-definer define-z3 lib #:default-make-fail make-not-available)
(provide define-z3)