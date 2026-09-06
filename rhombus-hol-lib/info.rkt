#lang info

(define collection 'multi)
(define deps '("base"
               ["rhombus-lib" #:version "1.1"]
               "rhombus-hol-kernel"))
(define pkg-desc "the derived layer of \"rhombus-hol\": tactics, conversions and the language surface, built over rhombus-hol-kernel")
(define license '0BSD)
(define version "0.1")
(define language-families '("Rhombus"))
