#lang rosette/safe
(require "ir.rkt")
(require "acc-semantics.rkt")

(require (only-in racket
                  hash
                  make-hash
                  hash-has-key?
                  hash-ref
                  hash-set!
                  for
                  ))
(require rosette/lib/match)

(require rosette/solver/smt/z3)
(current-solver (z3 
  #:logic 'QF_AUFBV 
  #:options (hash
   ':parallel.enable 'true
   ':parallel.threads.max 16)))

(define-block acc-v
(decl
  (0 (HOLE 1 (list "op") "add_op"))
  (1 (HOLE 1 (list "op") "branch_op"))
  (2 (INPUT 1 "clk"))
  (3 (HOLE 1 (list "op") "write_acc"))
  (4 (HOLE 1 (list "op") "write_mem"))
  (5 (MEMORY 32 16 "dmem"))
  (6 (MEMORY 32 16 "imem"))
  (8 (REGISTER 32 0 "acc"))
  (10 (REGISTER 16 0 "pc")))
(stmt
  (5 (WRITE (MUX 4 (CONST 0 16) (SEL (READ 6 10) (SLICE 16 31))) (MUX 4 (CONST 0 32) 8) (MUX 4 (CONST 0 32) (CONST -1 32))))
  (8 (:= (MUX 3 8 (MUX 0 (READ 5 (SEL (READ 6 10) (SLICE 16 31))) (ADD (READ 5 (SEL (READ 6 10) (SLICE 16 31))) 8)))))
  (10 (:= (MUX (AND 1 (LOGIC-NOT 8)) (ADD 10 (CONST 1 16)) (SEL (READ 6 10) (SLICE 16 31)))))))

(define acc-pre
  (hash 
    "load" (EQ (ID "op") (CONST 0 2))
    "add" (EQ (ID "op") (CONST 1 2))
    "store" (EQ (ID "op") (CONST 2 2))
    "brz" (EQ (ID "op") (CONST 3 2))))

(define (exp->verilog exp)
  (match exp
    [(ID n)      (format "~a" n)]
    [(CONST v w) (format "~a'd~a" w v)]
    [(EQ a b)    (format "(~a == ~a)" (exp->verilog a) (exp->verilog b))]
    [(XOR a b)   (format "(~a ^ ~a)" (exp->verilog a) (exp->verilog b))]
    [(AND a b)   (format "(~a & ~a)" (exp->verilog a) (exp->verilog b))]
    [_           (format "")]))

(define op-vals (synth-instrs!  
                #:semantics acc-semantics
                #:steps 1
                #:sketch acc-v
                #:reg-state (list "pc" "acc")
                #:mem-state (list "imem" "dmem")
                ))

(define hole-exps (make-hash))
(for ([(op holes) op-vals])
     (for ([(h v) holes])
          (let ([logic
                  (cond
                    [(and (concrete? (car v)) (not (bvzero? (car v))))
                     => (hash-ref acc-pre op)]
                    [else => null])])
          (cond
            [(null? logic)
              => (void)]
            [(hash-has-key? hole-exps h)
              => (hash-set! hole-exps h (XOR (hash-ref hole-exps h)
                                             logic))]
            [else
              => (hash-set! hole-exps h logic)]))))

(for ([(h e) hole-exps])
     (printf "assign ~a = ~a;~n" h (exp->verilog e)))
