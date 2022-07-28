#lang rosette/safe
(require "util.rkt")
(provide (all-defined-out))

(require (only-in racket
                  hash
                  ))

(define (load-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assume
      (bveq (extract 1 0 ir)
            (bv #b00 2)))))

(define (load-post pre post ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assert
      (equal? (post (ports "pc"))
              (bvadd1 (pre (ports "pc")))))
    (assert 
      (equal? (post (ports "acc"))
              (apply (vector-ref (pre (ports "dmem")) 0)
                     (list (extract 31 16 ir)))))
    (assert
      (equal? (vector-ref (post (ports "dmem")) 1)
              (vector-ref (pre (ports "dmem")) 1)))))

(define (add-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assume 
      (bveq (extract 1 0 ir)
            (bv #b01 2)))))

(define (add-post pre post ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assert
      (equal? (post (ports "pc"))
              (bvadd1 (pre (ports "pc")))))
    (assert 
      (equal? (post (ports "acc"))
              (bvadd (pre (ports "acc"))
                     (apply (vector-ref (pre (ports "dmem")) 0)
                            (list (extract 31 16 ir))))))
    (assert
      (equal? (vector-ref (post (ports "dmem")) 1)
              (vector-ref (pre (ports "dmem")) 1)))))

(define (store-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assume 
      (bveq (extract 1 0 ir)
            (bv #b10 2)))))

(define (store-post pre post ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assert
      (equal? (post (ports "pc"))
              (bvadd1 (pre (ports "pc")))))
    (assert 
      (equal? (post (ports "acc"))
              (pre (ports "acc"))))
    (assert
         (equal? (assoc-bv (extract 31 16 ir)
                           (vector-ref (post (ports "dmem")) 1))
                 (cons (extract 31 16 ir) (pre (ports "acc")))))
    ))

(define (brz-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assume 
      (bveq (extract 1 0 ir)
            (bv #b11 2)))))

(define (brz-post pre post ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (pre (ports "pc"))))])
    (assert
      (equal? (post (ports "pc"))
              (if (bvzero? (pre (ports "acc")))
                  (extract 31 16 ir)
                  (bvadd1 (pre (ports "pc"))))))
    (assert 
      (equal? (post (ports "acc"))
              (pre (ports "acc"))))
    (assert
      (equal? (vector-ref (post (ports "dmem")) 1)
              (vector-ref (pre (ports "dmem")) 1)))))

(define acc-semantics
(hash
"load" (list load-pre load-post)
"add" (list add-pre add-post)
"store" (list store-pre store-post)
"brz" (list brz-pre brz-post)
))
