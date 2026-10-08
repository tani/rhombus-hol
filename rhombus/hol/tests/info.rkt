#lang info

(define module-suffixes '(#"rhm"))

;; These replay the full standard theory sequence (several minutes each);
;; CI runs them in the separate `theories` job.
(define test-omit-paths '("golden" "upstream"))
