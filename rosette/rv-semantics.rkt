#lang rosette/safe
(require "util.rkt")
(provide (all-defined-out))

(require (only-in racket
                  hash
                  ))

;; ~~~ R-type ~~~ ;;
(define (R-pre pre ports op funct3 funct7)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            op))
    (assume 
      (bveq (extract 14 12 ir)
            funct3))
    (assume
      (bveq (extract 31 25 ir)
            funct7))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (R-post pre post ports op) 
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply op (list Rrs1 Rrs2)))))

       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; add
(define (add-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x0 3)
         (bv #x00 7)))

(define (add-post pre post ports)
  (R-post pre post ports 
          bvadd))

;; sub
(define (sub-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x0 3)
         (bv #x20 7)))

(define (sub-post pre post ports)
  (R-post pre post ports 
          bvsub))

;; xor
(define (xor-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x4 3)
         (bv #x00 7)))

(define (xor-post pre post ports)
  (R-post pre post ports 
          bvxor))

;; or
(define (or-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x6 3)
         (bv #x00 7)))

(define (or-post pre post ports)
  (R-post pre post ports 
          bvor))

;; and
(define (and-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x7 3)
         (bv #x00 7)))

(define (and-post pre post ports)
  (R-post pre post ports 
          bvand))

;; slt
(define (slt-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x2 3)
         (bv #x00 7)))

(define (slt-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (zero-extend (signed-lt Rrs1 Rrs2) (bitvector 32)))))

       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; sltu
(define (sltu-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x3 3)
         (bv #x00 7)))

(define (sltu-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (bool->bitvector (bvult Rrs1 Rrs2) 32))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; sll
(define (sll-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x1 3)
         (bv #x00 7)))

(define (sll-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply bvshl (list Rrs1 (zero-extend
                                           (extract 4 0 Rrs2)
                                           (bitvector 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; srl
(define (srl-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x5 3)
         (bv #x00 7)))

(define (srl-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply bvlshr (list Rrs1 (zero-extend
                                           (extract 4 0 Rrs2)
                                           (bitvector 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; sra
(define (sra-pre pre ports)
  (R-pre pre ports 
         (bv #b0110011 7)
         (bv #x5 3)
         (bv #x20 7)))

(define (sra-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply bvashr (list Rrs1 (zero-extend
                                           (extract 4 0 Rrs2)
                                           (bitvector 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; ~~~ I-type ~~~ ;;
(define (I-pre pre ports op funct3)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            op))
    (assume 
      (bveq (extract 14 12 ir)
            funct3))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (I-post pre post ports op) 
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply op (list Rrs1 imm)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; addi
(define (addi-pre pre ports)
  (I-pre pre ports 
         (bv #b0010011 7)
         (bv #x0 3)))

(define (addi-post pre post ports)
  (I-post pre post ports 
          bvadd))

;; xori
(define (xori-pre pre ports)
  (I-pre pre ports 
         (bv #b0010011 7)
         (bv #x4 3)))

(define (xori-post pre post ports)
  (I-post pre post ports 
          bvxor))

;; ori
(define (ori-pre pre ports)
  (I-pre pre ports 
         (bv #b0010011 7)
         (bv #x6 3)))

(define (ori-post pre post ports)
  (I-post pre post ports 
          bvor))

;; andi
(define (andi-pre pre ports)
  (I-pre pre ports 
         (bv #b0010011 7)
         (bv #x7 3)))

(define (andi-post pre post ports)
  (I-post pre post ports 
          bvand))

;; rori
(define (rori-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0010011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #b101 3)))
    (assume 
      (bveq (extract 31 26 ir)
            (bv #b011000 6)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (rori-post pre post ports)
  (I-post pre post ports 
          rotater))

;; clz
(define (clz-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0010011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #b001 3)))
    (assume 
      (bveq (extract 31 20 ir)
            (bv #b011000000000 12)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

;; slli
(define (slli-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0010011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x1 3)))
    (assume 
      (bveq (extract 31 25 ir)
            (bv 0 7)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (slli-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply bvshl (list Rrs1 (zero-extend
                                           (extract 4 0 imm)
                                           (bitvector 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; srli
(define (srli-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0010011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x5 3)))
    (assume 
      (bveq (extract 31 25 ir)
            (bv 0 7)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))


(define (srli-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (extract 24 20 ir)]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply bvlshr (list Rrs1 (zero-extend 
                                                     imm
                                                     (bitvector 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; srai
(define (srai-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0010011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x5 3)))
    (assume 
      (bveq (extract 31 25 ir)
            (bv #x20 7)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (srai-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (extract 24 20 ir)]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (apply bvashr (list Rrs1 (zero-extend
                                                     imm
                                                     (bitvector 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; sltiu
(define (sltiu-pre pre ports)
  (I-pre pre ports 
         (bv #b0010011 7)
         (bv #x3 3)))

(define (sltiu-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (bool->bitvector (bvult Rrs1 imm) 32))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; slti
(define (slti-pre pre ports)
  (I-pre pre ports 
         (bv #b0010011 7)
         (bv #x2 3)))

(define (slti-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (zero-extend (signed-lt Rrs1 imm) (bitvector 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; lb
(define (lb-pre pre ports)
  (I-pre pre ports 
         (bv #b0000011 7)
         (bv #x0 3)))

(define (lb-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd 
                 (sign-extend
                   (extract 7 0
                      (bvlshr 
                        (apply (vector-ref (pre (ports "dmem")) 0)
                               (list (bvashr (bvadd Rrs1 imm) (bv 2 32))))
                        (concat (bv 0 27) (extract 1 0 (bvadd Rrs1 imm)) (bv 0 3))))
                   (bitvector 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; lh
(define (lh-pre pre ports)
  (I-pre pre ports 
         (bv #b0000011 7)
         (bv #x1 3)))

(define (lh-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd 
                 (sign-extend
                   (extract 15 0
                      (bvlshr 
                        (apply (vector-ref (pre (ports "dmem")) 0)
                               (list (bvashr (bvadd Rrs1 imm) (bv 2 32))))
                        (concat (bv 0 27) (extract 1 0 (bvadd Rrs1 imm)) (bv 0 3))))
                   (bitvector 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; lw
(define (lw-pre pre ports)
  (I-pre pre ports 
         (bv #b0000011 7)
         (bv #x2 3)))

(define (lw-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd 
                 (apply (vector-ref (pre (ports "dmem")) 0)
                        (list (bvashr (bvadd Rrs1 imm) (bv 2 32)))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; lbu
(define (lbu-pre pre ports)
  (I-pre pre ports 
         (bv #b0000011 7)
         (bv #x4 3)))

(define (lbu-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd 
                 (zero-extend
                   (extract 7 0
                      (bvlshr 
                        (apply (vector-ref (pre (ports "dmem")) 0)
                               (list (bvashr (bvadd Rrs1 imm) (bv 2 32))))
                        (concat (bv 0 27) (extract 1 0 (bvadd Rrs1 imm)) (bv 0 3))))
                   (bitvector 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; lhu
(define (lhu-pre pre ports)
  (I-pre pre ports 
         (bv #b0000011 7)
         (bv #x5 3)))

(define (lhu-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd 
                 (zero-extend
                   (extract 15 0
                      (bvlshr 
                        (apply (vector-ref (pre (ports "dmem")) 0)
                               (list (bvashr (bvadd Rrs1 imm) (bv 2 32))))
                        (concat (bv 0 27) (extract 1 0 (bvadd Rrs1 imm)) (bv 0 3))))
                   (bitvector 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; sb
(define (sb-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0100011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x0 3)))))

(define (sb-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         [imm (sign-extend (concat
                             (extract 31 25 ir)
                             (extract 11 7 ir))
                           (bitvector 32))]
         [write-data (extract 7 0 Rrs2)]
         [offset (extract 1 0 (bvadd Rrs1 imm))]
         [read-data (apply (vector-ref (pre (ports "dmem")) 0)
                        (list (bvashr (bvadd Rrs1 imm) (bv 2 32))))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (vector-ref (post (ports "rf")) 1)
                 (vector-ref (pre (ports "rf")) 1)))

       (assert
         (equal? (assoc-bv (bvashr (bvadd Rrs1 imm) (bv 2 32))
                           (vector-ref (post (ports "dmem")) 1))
                 (cons (bvashr (bvadd Rrs1 imm) (bv 2 32))
                 (cond
                   [(bveq offset (bv 0 2)) (concat (extract 31 8 read-data) write-data)]
                   [(bveq offset (bv 1 2)) (concat (extract 31 16 read-data) write-data (extract 7 0 read-data))]
                   [(bveq offset (bv 2 2)) (concat (extract 31 24 read-data) write-data (extract 15 0 read-data))]
                   [else (concat write-data (extract 23 0 read-data))]))))
       )))

;; sh
(define (sh-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0100011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x1 3)))))

(define (sh-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         [imm (sign-extend (concat
                             (extract 31 25 ir)
                             (extract 11 7 ir))
                           (bitvector 32))]
         [write-data (extract 15 0 Rrs2)]
         [offset (extract 1 0 (bvadd Rrs1 imm))]
         [read-data (apply (vector-ref (pre (ports "dmem")) 0)
                        (list (bvashr (bvadd Rrs1 imm) (bv 2 32))))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (vector-ref (post (ports "rf")) 1)
                 (vector-ref (pre (ports "rf")) 1)))

       (assert
         (equal? (assoc-bv (bvashr (bvadd Rrs1 imm) (bv 2 32))
                           (vector-ref (post (ports "dmem")) 1))
                 (cons (bvashr (bvadd Rrs1 imm) (bv 2 32))
                 (cond
                   [(bveq offset (bv 0 2)) => (concat (extract 31 16 read-data) write-data)]
                   [(bveq offset (bv 1 2)) => (concat (extract 31 24 read-data) write-data (extract 7 0 read-data))]
                   [else => (concat write-data (extract 15 0 read-data))]))))
       )))

;; sw
(define (sw-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0100011 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x2 3)))))

(define (sw-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         [imm (sign-extend (concat
                             (extract 31 25 ir)
                             (extract 11 7 ir))
                           (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (vector-ref (post (ports "rf")) 1)
                 (vector-ref (pre (ports "rf")) 1)))

       (assert
         (equal? (assoc-bv (bvashr (bvadd Rrs1 imm) (bv 2 32))
                                (vector-ref (post (ports "dmem")) 1))
                 (cons (bvashr (bvadd Rrs1 imm) (bv 2 32)) Rrs2)))
        )))

(define (B-pre pre ports op funct3)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            op))
    (assume 
      (bveq (extract 14 12 ir)
            funct3))))

(define (B-post pre post ports op)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         [imm (sign-extend (concat
                (bit 31 ir)
                (bit 7 ir)
                (extract 30 25 ir)
                (extract 11 8 ir)
                (bv 0 1))
                (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (if (apply op (list Rrs1 Rrs2))
                 (bvadd
                   (pre (ports "pc"))
                   imm)
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32)))))

       (assert
         (equal? (vector-ref (post (ports "rf")) 1)
                 (vector-ref (pre (ports "rf")) 1)))
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; beq
(define (beq-pre pre ports)
  (B-pre pre ports
         (bv #b1100011 7)
         (bv #x0 3)))

(define (beq-post pre post ports)
  (B-post pre post ports
         bveq))

;; bne
(define (bne-pre pre ports)
  (B-pre pre ports
         (bv #b1100011 7)
         (bv #x1 3)))

(define (bne-post pre post ports)
  (B-post pre post ports
          (compose not (curry bveq))))

;; blt
(define (blt-pre pre ports)
  (B-pre pre ports
         (bv #b1100011 7)
         (bv #x4 3)))

(define (blt-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         [imm (sign-extend (concat
                (bit 31 ir)
                (bit 7 ir)
                (extract 30 25 ir)
                (extract 11 8 ir)
                (bv 0 1))
                (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (if (bvzero? (signed-lt Rrs1 Rrs2))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))
                 (bvadd
                   (pre (ports "pc"))
                   imm))))

       (assert
         (equal? (vector-ref (post (ports "rf")) 1)
                 (vector-ref (pre (ports "rf")) 1)))
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; bge
(define (bge-pre pre ports)
  (B-pre pre ports
         (bv #b1100011 7)
         (bv #x5 3)))

(define (bge-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rs1 (extract 19 15 ir)]
         [rs2 (extract 24 20 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [Rrs2 (if 
                (bvzero? rs2)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs2)))]
         [imm (sign-extend (concat
                (bit 31 ir)
                (bit 7 ir)
                (extract 30 25 ir)
                (extract 11 8 ir)
                (bv 0 1))
                (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (if 
                   (bvzero? (signed-lt Rrs1 Rrs2))
                 (bvadd
                   (pre (ports "pc"))
                   imm)
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32)))))

       (assert
         (equal? (vector-ref (post (ports "rf")) 1)
                 (vector-ref (pre (ports "rf")) 1)))
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; bltu
(define (bltu-pre pre ports)
  (B-pre pre ports
         (bv #b1100011 7)
         (bv #x6 3)))

(define (bltu-post pre post ports)
  (B-post pre post ports
          bvult))

;; bgeu
(define (bgeu-pre pre ports)
  (B-pre pre ports
         (bv #b1100011 7)
         (bv #x7 3)))

(define (bgeu-post pre post ports)
  (B-post pre post ports
          bvuge))

;; jal
(define (jal-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b1101111 7)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (jal-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [imm (sign-extend (concat
                (bit 31 ir)
                (extract 19 12 ir)
                (bit 20 ir)
                (extract 30 21 ir)
                (bv 0 1))
                (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   imm)))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (bvadd (pre (ports "pc")) (bv 4 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; jalr
(define (jalr-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b1100111 7)))
    (assume 
      (bveq (extract 14 12 ir)
            (bv #x0 3)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (jalr-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         [rs1 (extract 19 15 ir)]
         [Rrs1 (if 
                (bvzero? rs1)
                (bv 0 32)
                (apply (vector-ref (pre (ports "rf")) 0) 
                       (list rs1)))]
         [imm (sign-extend (extract 31 20 ir) (bitvector 32))]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   Rrs1
                   imm)))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (bvadd (pre (ports "pc")) (bv 4 32)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; lui
(define (lui-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0110111 7)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (lui-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         ;[imm (concat (extract 31 12 ir) (bv 0 12))]
         [imm (extract 31 12 ir)]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (concat imm (bv 0 12)))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

;; auipc
(define (auipc-pre pre ports)
  (let ([ir (apply (vector-ref (pre (ports "imem")) 0)
                   (list (bvlshr (pre (ports "pc")) (bv 2 32))))])
    (assume 
      (bveq (extract 6 0 ir)
            (bv #b0010111 7)))
    (assume ; rd =/= 0
      (not (bvzero? (extract 11 7 ir))))))

(define (auipc-post pre post ports)
  (let* (
         [ir (apply (vector-ref (pre (ports "imem")) 0)
                    (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         [rd (extract 11 7 ir)]
         ;[imm (concat (extract 31 12 ir) (bv 0 12))]
         [imm (extract 31 12 ir)]
         )
    (begin 
       (assert
         (equal? (post (ports "pc"))
                 (bvadd
                   (pre (ports "pc"))
                   (bv 4 32))))

       (assert
         (equal? (assoc-bv rd 
                           (vector-ref (post (ports "rf")) 1))
                 (cons rd (bvadd
                            (pre (ports "pc"))
                            (concat imm (bv 0 12))))))
                         
       (assert
         (equal? (vector-ref (post (ports "dmem")) 1)
                 (vector-ref (pre (ports "dmem")) 1)))
       )))

(define rv-semantics
(hash
"add" (list add-pre add-post)
"sub" (list sub-pre sub-post)
"xor" (list xor-pre xor-post)
"or" (list or-pre or-post)
"and" (list and-pre and-post)
"slt" (list slt-pre slt-post)
"sltu" (list sltu-pre sltu-post)
"sll" (list sll-pre sll-post)
"srl" (list srl-pre srl-post)
"sra" (list sra-pre sra-post)
"addi" (list addi-pre addi-post)
"xori" (list xori-pre xori-post)
"ori" (list ori-pre ori-post)
"andi" (list andi-pre andi-post)
"slli" (list slli-pre slli-post)
"srli" (list srli-pre srli-post)
"srai" (list srai-pre srai-post)
"sltiu" (list sltiu-pre sltiu-post)
"slti" (list slti-pre slti-post)
"lb" (list lb-pre lb-post)
"lh" (list lh-pre lh-post)
"lw" (list lw-pre lw-post)
"lbu" (list lbu-pre lbu-post)
"lhu" (list lhu-pre lhu-post)
"sb" (list sb-pre sb-post)
"sh" (list sh-pre sh-post)
"sw" (list sw-pre sw-post)
"beq" (list beq-pre beq-post)
"bne" (list bne-pre bne-post)
"blt" (list blt-pre blt-post)
"bge" (list bge-pre bge-post)
"bltu" (list bltu-pre bltu-post)
"bgeu" (list bgeu-pre bgeu-post)
"jal" (list jal-pre jal-post)
"jalr" (list jalr-pre jalr-post)
"lui" (list lui-pre lui-post)
"auipc" (list auipc-pre auipc-post)
))

