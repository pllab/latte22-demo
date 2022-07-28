#lang rosette/safe
(require (only-in racket
                  values
                  for
                  for/list
                  range
                  ))
(provide (all-defined-out))

;; association lists
(define (acons k v a)
  (cons (cons k v) a))

(define (assoc-bv v a)
  (assf (lambda (x) (bveq x v)) a))

;; symbolics
(define (new-sym w)
  (define-symbolic* x (bitvector w))
  x)

(define (bvwidth x)
  (length (bitvector->bits x)))

;; circuit helpers
(define (one-bit-add a b cin)
  (assert (and (equal? (bvwidth a) 1)
               (equal? (bvwidth b) 1)))
  (let* ([sumbit (bvxor (bvxor a b) cin)]
         [cout (bvor (bvand a b)
                     (bvand a cin)
                     (bvand b cin))])
    (values sumbit cout)))

(define (add-helper a b cin)
  (let* ([max-width (max (bvwidth a) (bvwidth b))]
         [ext-a (zero-extend a (bitvector max-width))]
         [ext-b (zero-extend b (bitvector max-width))])
    (cond [(equal? (bvwidth ext-a) 1) (one-bit-add ext-a ext-b cin)]
          [else
                (let*-values 
                  ([(lsbit ripplecarry) (one-bit-add (bit 0 ext-a)
                                                     (bit 0 ext-b)
                                                     cin)]
                   [(msbits cout) (add-helper (extract (sub1 max-width) 1 ext-a)
                                              (extract (sub1 max-width) 1 ext-b)
                                              ripplecarry)])
                  (values (concat msbits lsbit) cout))])))

(define (basic-add a b)
  (let-values ([(sumbits cout) (add-helper a b (bv 0 1))])
    (concat cout sumbits)))

(define (basic-sub a b)
  (let-values ([(sumbits cout) (add-helper a (bvnot b) (bv 1 1))])
    (concat cout sumbits)))

(define (basic-lt a b)
  (assert (equal? (bvwidth a) (bvwidth b)))
  (cond [(= (bvwidth a) 1)
         (bvand b (bvnot a))]
        [else
         (let* ([max-width (max (bvwidth a) (bvwidth b))]
                [small (basic-lt (extract (- max-width 2) 0 a)
                                 (extract (- max-width 2) 0 b))])
                (bvor (bvand (msb b) (bvnot (msb a)))
                      (bvand small
                             (bvnot (bvxor (msb a) (msb b))))))]))

(define (basic-gt a b)
  (basic-lt b a))

(define (basic-eq a b)
  (let ([a^b (bitvector->bits (bvxor a b))])
    (bvnot (foldl bvor (car a^b) (cdr a^b)))))

;; PyRTL's signed lt:
;    a, b = match_bitwidth(as_wires(a), as_wires(b), signed=True)
;    r = a - b
;    return r[-1] ^ (~a[-1]) ^ (~b[-1])
(define (signed-lt a b)
  (let* ([max-width (max (bvwidth a)
                         (bvwidth b))]
         [a_ (sign-extend a (bitvector max-width))]
         [b_ (sign-extend b (bitvector max-width))]
         [r  (basic-sub a_ b_)])
    (bvxor
      (msb r)
      (bvnot (msb a_))
      (bvnot (msb b_)))))

(define (clmul a_ b_)
  (let* ([w (max (bvwidth a_) (bvwidth b_))]
         [a (zero-extend a_ (bitvector w))]
         [b (zero-extend b_ (bitvector w))]
         [result (bv 0 w)])
    (for ([i (range w)])
         (cond [(not (bvzero? (bit i b)))
                (set! result (bvxor result (bvshl a (bv i w))))]))
    result))

(define (clmulh a_ b_)
  (let* ([w (max (bvwidth a_) (bvwidth b_))]
         [a (zero-extend a_ (bitvector w))]
         [b (zero-extend b_ (bitvector w))])
    (define result (bv 0 w))
    (for ([i (range w)])
         (cond [(not (bvzero? (bit i b)))
                (set! result (bvxor result (bvlshr a (bv (- w i) w))))]))
    result))

(define (andn a b)
  (bvand a (bvnot b)))

(define (orn a b)
  (bvor a (bvnot b)))

(define (xnor a b)
  (bvnot (bvxor a b)))

(define (pack a b)
  (concat (extract 15 0 b) (extract 15 0 a)))

(define (packh a b)
  (zero-extend (concat (extract 7 0 b) (extract 7 0 a)) (bitvector 32)))

(define (rotatel a b)
  (define w (bvwidth a))
  (bvrol a (zero-extend (extract 4 0 b) (bitvector w))))

(define (rotater a b)
  (bvror a (zero-extend (extract 4 0 b) (bitvector 32))))

(define (count-zero a msb)
  (define (cz b) 
    (cond 
      [(null? b) (bv 0 32)]
      [(bvzero? (car b)) (bvadd1 (cz (cdr b)))]
      [else (bv 0 32)]))
  (cz (cond [msb (reverse (bitvector->bits a))]
            [else (bitvector->bits a)])))

(define (count-ones a)
  (foldl bvadd (bv 0 32) 
         (map (lambda (x) (zero-extend x (bitvector 32))) (bitvector->bits a))))

(define (zip32 a)
  (define result (concat (bit 16 a) (bit 0 a)))
  (for ([i (range 1 16)])
    (set! result (concat (bit (+ i 16) a) (bit i a) result)))
  result)

(define (unzip32 a)
  (define result (bit 0 a))
  (for ([i (range 1 16)])
    (set! result (concat (bit (* i 2) a) result)))
  (for ([i (range 0 16)])
    (set! result (concat (bit (add1 (* i 2)) a) result)))
  result)

(define (revb a)
  (concat
    (extract 8 1 (foldl concat (bv 0 1) (reverse (bitvector->bits (extract 31 24 a)))))
    (extract 8 1 (foldl concat (bv 0 1) (reverse (bitvector->bits (extract 23 16 a)))))
    (extract 8 1 (foldl concat (bv 0 1) (reverse (bitvector->bits (extract 15 8 a)))))
    (extract 8 1 (foldl concat (bv 0 1) (reverse (bitvector->bits (extract 7 0 a)))))))

(define (rev8 a)
  (concat
    (extract 7 0 a)
    (extract 15 8 a)
    (extract 23 16 a)
    (extract 31 24 a)))
