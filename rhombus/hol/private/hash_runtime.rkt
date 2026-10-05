#lang racket/base
;; Copyright 1996 INRIA; based on Xavier Leroy, OCaml 4.14.1 runtime/hash.c.
;; Modified 2026-10-05: HOL data-model subset in Racket.
;; LGPL-2.1 with OCaml linking exception; see ../../../THIRD_PARTY_LICENSES/OCaml.txt.
;; Compatible subset of OCaml 4.14.1 runtime/hash.c for HOL data.
;; Based on the MurmurHash3 mixing and bounded breadth-first traversal.
;; OCaml runtime code: copyright INRIA; LGPL-2.1 with OCaml linking exception.
;; See ../../../THIRD_PARTY_LICENSES/OCaml.txt. This helper cannot construct kernel values.
(provide block immediate hash_model)
(struct block (tag fields) #:transparent)
(struct immediate (value) #:transparent)
(define mask #xffffffff)
(define (u32 v) (bitwise-and v mask))
(define (rotl v n) (u32 (bitwise-ior (arithmetic-shift v n) (arithmetic-shift v (- n 32)))))
(define (mix h d)
  (define d1 (u32 (* d #xcc9e2d51)))
  (define d2 (u32 (* (rotl d1 15) #x1b873593)))
  (u32 (+ (* (rotl (bitwise-xor h d2) 13) 5) #xe6546b64)))
(define (mix-int h d)
  (mix h (u32 (bitwise-xor (arithmetic-shift d -32) (arithmetic-shift d -63) d))))
(define (mix-string h s)
  (define bs (string->bytes/utf-8 s))
  (define len (bytes-length bs))
  (define h1
    (for/fold ([h h]) ([i (in-range 0 len 4)])
      (define end (min (+ i 4) len))
      (define w (for/fold ([w 0]) ([j (in-range i end)])
                  (bitwise-ior w (arithmetic-shift (bytes-ref bs j) (* 8 (- j i))))))
      (mix h w)))
  (bitwise-xor h1 len))
(define (finish h)
  (define a (u32 (* (bitwise-xor h (arithmetic-shift h -16)) #x85ebca6b)))
  (define b (u32 (* (bitwise-xor a (arithmetic-shift a -13)) #xc2b2ae35)))
  (bitwise-and (bitwise-xor b (arithmetic-shift b -16)) #x3fffffff))
(define (hash_model obj)
  (define queue (make-vector 100 #f))
  (vector-set! queue 0 obj)
  (let loop ([rd 0] [wr 1] [num 10] [h 0])
    (cond
      [(or (= rd wr) (= num 0)) (finish h)]
      [else
       (define v (vector-ref queue rd))
       (cond
         [(immediate? v) (loop (add1 rd) wr (sub1 num) (mix-int h (bitwise-ior (arithmetic-shift (immediate-value v) 1) 1)))]
         [(string? v) (loop (add1 rd) wr (sub1 num) (mix-string h v))]
         [(block? v)
          (define h1 (mix h (+ (arithmetic-shift (length (block-fields v)) 10) (block-tag v))))
          (define wr1 (for/fold ([wr wr]) ([f (in-list (block-fields v))] #:break (= wr 100))
                        (vector-set! queue wr f) (add1 wr)))
          (loop (add1 rd) wr1 num h1)]
         [else (error 'hash_model "unsupported host value")])]))

)