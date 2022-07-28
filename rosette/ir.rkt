#lang rosette/safe
(require "util.rkt")

(require (only-in racket
                  range
                  make-vector
                  vector-copy
                  for
                  for/list
                  for/hash
                  make-list
                  in-naturals
                  hash
                  make-hash
                  hash-set!
                  hash-has-key?
                  hash-ref
                  hash-keys
                  values
                  set!-values
                  string-contains?
                  define-values
                  let-values
                  ))

(require racket/struct)
(require rosette/lib/match)
(require rosette/lib/angelic rosette/lib/synthax)

(provide (all-defined-out))
(current-grammar-depth 2)

(struct block (decls stmts)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (obj) 'block)
      (lambda (obj) (list (block-decls obj)
                          (block-stmts obj)))))])

(struct INPUT (bitwidth name) #:transparent)
(struct OUTPUT (bitwidth name) #:transparent)
(struct REGISTER (bitwidth default name) #:transparent)
(struct MEMORY (bitwidth addrwidth name) #:transparent)
(struct ROM (bitwidth addrwidth data name) #:transparent)
(struct CONST (value bitwidth) #:transparent)
(struct := (w) #:transparent)
(struct AND (w0 w1) #:transparent)
(struct LOGIC-AND (w0 w1) #:transparent)
(struct OR (w0 w1) #:transparent)
(struct LOGIC-OR (w0 w1) #:transparent)
(struct REDUCE-OR (wires) #:transparent)
(struct REDUCE-BOOL (wires) #:transparent)
(struct XOR (w0 w1) #:transparent)
(struct NAND (w0 w1) #:transparent)
(struct NOT (w0) #:transparent)
(struct LOGIC-NOT (w0) #:transparent)
(struct ADD (w0 w1) #:transparent)
(struct ADD-CARRY (w0 w1) #:transparent)
(struct SUB (w0 w1) #:transparent)
(struct SUB-CARRY (w0 w1) #:transparent)
(struct MULT (w0 w1) #:transparent)
(struct EQ (w0 w1) #:transparent)
(struct NE (w0 w1) #:transparent)
(struct LT (w0 w1) #:transparent)
(struct GT (w0 w1) #:transparent)
(struct GE (w0 w1) #:transparent)
(struct SHL (w0 w1) #:transparent)
(struct SHR (w0 w1) #:transparent)
(struct SSHR (w0 w1) #:transparent)
(struct MUX (sel w0 w1) #:transparent)
(struct WITH (sel t f) #:transparent)
(struct CONCAT (wires) #:transparent)
(struct SEL (w0 sel) #:transparent)
(struct SLICE (l h) #:transparent)
(struct READ (id addr) #:transparent)       ; read address `addr` of mem-block `id`
(struct WRITE (addr data we) #:transparent) ; write `data` to mem-block at `addr`
                                            ; req. write enable (`we`)
(struct READ-ASSOC (id addr) #:transparent)
(struct WRITE-ASSOC (addr data we) #:transparent)
(struct HOLE (width terminals name) #:transparent)
(struct ID (name) #:transparent)

(define (slice-range l h r)
  (drop-right (drop (range r) l) (- r h)))

(define-syntax-rule (decl (id args) ...)
  `((,id ,args) ...))

(define-syntax-rule (stmt (out op) ...)
  `((out ,op) ...))

(define-syntax-rule (define-block name decls stmts)
  (define name
    (block decls stmts)))

(define (build-ports-map decls)
  (define ports-map (make-hash))
  (for ([d decls])
    (let ([id (first d)] [args (second d)])
      (match args
             [(INPUT _ n) (hash-set! ports-map n id)]
             [(OUTPUT _ n) (hash-set! ports-map n id)]
             [(REGISTER _ _ n) (hash-set! ports-map n id)]
             [(MEMORY _ _ n) (hash-set! ports-map n id)]
             [(ROM _ _ _ n) (hash-set! ports-map n id)]
             [(HOLE _ _ n) (hash-set! ports-map n id)])))
  ports-map)

(define (build-sym-inputs decls)
  (define symputs (make-hash))
  (for ([d decls])
    (let ([id (first d)] [args (second d)])
      (match args
             [(INPUT w _) (hash-set! symputs id (new-sym w))]
             [(REGISTER w _ _) (hash-set! symputs id (new-sym w))]
             ;[(HOLE w _ _) (hash-set! symputs id (new-sym w))]
             [(MEMORY bw aw n)
              (begin (define-symbolic* mem (~> (bitvector aw) (bitvector bw)))
              (hash-set! symputs id (vector mem null)))]
             [_ #f])))
  symputs)

(define (setup-env net default-val steps inputs)
  ; overapproximation
  (define max-out (apply max (for/list ([s (block-stmts net)]) 
                                       (match s [(list out _) out]))))
  (define decl-count (apply max (for/list ([s (block-decls net)]) 
                                       (match s [(list out _) out]))))
  (set! max-out (max max-out decl-count))
  (define env (make-vector (add1 max-out) #f))
  (define (store i v) (vector-set! env i v))
  (define regmap (make-hash))
  (define holemap (make-vector steps #f))
  (define hole-env (make-vector (add1 decl-count) (make-list steps #f)))

  (for ([s (block-decls net)])
    (match s
      [(list out op)
       (match op
        [(HOLE w _ _) (vector-set! hole-env
                                  out
                                  (map new-sym (make-list steps w)))]
        [_ (void)])]))
  ;(printf "hole-env ~a~n" hole-env)

  (define (unzip lst [acc '()])
    (if (or (empty? lst) (empty? (car lst)))
      (reverse acc)
      (unzip (map cdr lst) (cons (map car lst) acc))))
  (define unzipped-holes (unzip (vector->list hole-env)))
  ;(printf "unzip ~a~n" unzipped-holes)

  (for ([i (range steps)])
       (vector-set! holemap i (list->vector (list-ref unzipped-holes i))))

  (for ([d (block-decls net)])
    (let ([id (first d)] [args (second d)])
      ;(printf "~a ~a~n" id args)
      (store id
             (match args
               [(INPUT w _) 
                (cond [(hash-has-key? inputs id) (hash-ref inputs id)]
                      [else #f])]
               [(REGISTER w val _) ;(integer->bitvector val (bitvector w))]
                (cond [(hash-has-key? inputs id) (hash-ref inputs id)]
                      [else (let ([reg-val (new-sym w)])
                                     (begin (hash-set! regmap id reg-val)
                                          ;  reg-val))])]
                                          (integer->bitvector val (bitvector w))))])]
               [(HOLE _ _ _) (cond [(hash-has-key? inputs id)
                                    (hash-ref inputs id)]
                                   [else (vector-ref (vector-ref holemap 0) id)])]
               [(MEMORY bw aw _)
                (cond [(hash-has-key? inputs id) (hash-ref inputs id)]
                      [else #f])]
               [(ROM bw aw data _) 
                (begin (define rom null)
                       (for ([datum data]
                             [index (in-naturals)])
                            (set! rom (acons (integer->bitvector index (bitvector aw))
                                             (integer->bitvector datum (bitvector bw))
                                             rom)))
                       rom)]
               [(OUTPUT w _) (bv default-val w)]))))
  (values env regmap holemap))

(define (update-env env inputs regmap holemap)
  (define (store i v) (vector-set! env i v))
  (for ([(i val) inputs])
    (store i val))
  (for ([(r next) regmap])
    (cond [r    (store r next)]
          [else (void)]))
  (for ([h (filter (lambda (x) (not (empty? x))) 
                   (for/list ([x holemap] [i (in-naturals)]) 
                             (if x (list i x) (list))))])
    (store (first h) (second h)))
  env)

(define (print-env decls env)
  (define (load i) (vector-ref env i))
  (for ([d decls])
    (let* ([id (first d)] [args (second d)])
      (match args
        [(REGISTER _ _ n) (printf "REG ~a: ~a~n" n (load id))]
        [(MEMORY _ _  n)  (printf "MEM ~a: ~a~n" n (load id))]
                          ;(printf "MEM ~a: ~n~a~n" n 
                          ;       (for/list ([mems (load id)])
                          ;            (format "  ~a -> ~a~n" (car mems) (cdr mems))))]
        [(ROM _ _ _ n)    (printf "ROM ~a: ~a~n" n (load id))]
        [(OUTPUT _ n)     (printf "OUT ~a: ~a~n" n (load id))]
        [(HOLE _ _ n)     (printf "HOLE ~a: ~a~n" n (load id))]
        [(INPUT _ n)      (printf "IN ~a: ~a~n" n (load id))]
        [_                (printf "")])))
  (printf "-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=~n"))

(define (print-holes decls holemap steps)
  (for ([d decls])
    (let* ([id (first d)] [args (second d)])
      (match args
        [(HOLE _ _ n) (printf "~a: ~a~n" n
                              (for/list ([i (range steps)])
                                        (vector-ref (vector-ref holemap i) id)))]
        [_ (printf "")])))
  (printf "-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=~n"))

(define (get-holes decls holemap steps)
  (define hole-values (make-hash))
  (for ([d decls])
    (let* ([id (first d)] [args (second d)])
      (match args
        [(HOLE _ _ n) (hash-set! hole-values n
                              (for/list ([i (range steps)])
                                        (vector-ref (vector-ref holemap i) id)))]
        [_ (void)])))
  hole-values)

(define (interpret program env regmap)

  (define (store i v) (vector-set! env i v))
  (define (load i) (vector-ref env i))
  (define decls (block-decls program))

  (define (mem-data-width i)
    (let decl-search ([d decls])
      (if (car d)
        (let ([id (first (car d))] [args (second (car d))])
          (cond [(= i id)
                 (match args
                        [(MEMORY bw _ _) bw]
                        [_ #f])]
                [else (decl-search (cdr d))]))
        #f)))

  (define (net-eval exp)
    (match exp
      [(? bv?)        exp]
      [(? integer?)   (load exp)]
      [(CONST v w)    (integer->bitvector v (bitvector w))]
      [(:= w)         (net-eval w)]
      [(AND a b)      (bvand (net-eval a) (net-eval b))]
      [(LOGIC-AND a b) (bool->bitvector (&& (bitvector->bool (net-eval a)) (bitvector->bool (net-eval b))))]
      [(OR a b)       (bvor (net-eval a) (net-eval b))]
      [(LOGIC-OR a b) (bool->bitvector (|| (bitvector->bool (net-eval a)) (bitvector->bool (net-eval b))))]
      [(REDUCE-OR ws) (apply bvor (for/list ([a ws]) (net-eval a)))]
      [(REDUCE-BOOL ws) (apply bvor (for/list ([a ws]) (net-eval a)))]
      [(XOR a b)      (bvxor (net-eval a) (net-eval b))]
      [(NAND a b)     (bvnot (bvand (net-eval a) (net-eval b)))]
      [(NOT a)        (bvnot (net-eval a))]
      [(LOGIC-NOT a)  (bool->bitvector (bvzero? (net-eval a)))]
      [(ADD a b)      (let ([a_ (net-eval a)]
                            [b_ (net-eval b)])
                        (bvadd a_ b_))]
      [(ADD-CARRY a b) (let ([a_ (net-eval a)]
                             [b_ (net-eval b)])
                         (basic-add a_ b_))]
      [(SUB a b)      (let ([a_ (net-eval a)]
                            [b_ (net-eval b)])
                        (bvsub a_ b_))]
      [(SUB-CARRY a b) (let ([a_ (net-eval a)]
                             [b_ (net-eval b)])
                         (basic-sub a_ b_))]
      [(MULT a b)     (bvmul (net-eval a) (net-eval b))]
      [(EQ a b)       (basic-eq (net-eval a) (net-eval b))] 
      [(NE a b)       (bvnot (basic-eq (net-eval a) (net-eval b)))] 
      [(LT a b)       (basic-lt (net-eval a) (net-eval b))]
      [(GT a b)       (basic-gt (net-eval a) (net-eval b))] 
      [(GE a b)       (bvor (basic-gt (net-eval a) (net-eval b))
                            (basic-eq (net-eval a) (net-eval b)))] 
      [(SHL a b)      (bvshl (net-eval a) (net-eval b))] 
      [(SHR a b)      (bvlshr (net-eval a) (net-eval b))] 
      [(SSHR a b)     (bvashr (net-eval a) (net-eval b))] 
      [(CONCAT wires) (let concatter ([wl wires])
                        (if (= (length wl) 1)
                            (net-eval (car wl))
                            (concat (net-eval (car wl)) (concatter (cdr wl)))))]
      [(SEL a sel)  (let ([selectee (net-eval a)])
                      (match sel
                        [(SLICE l h) (extract h l selectee)]
                        [(? list?) 
                         (apply concat 
                                (for/list ([i (reverse sel)])
                                  (bit i selectee)))]))]
      [(MUX sel a b)  (if (bvzero? (net-eval sel)) (net-eval a) (net-eval b))]
      [(WITH c t f)   (cond [(bvzero? (net-eval c)) (net-eval f)]
                            [else (net-eval t)])]
      ;[(READ id addr)
      ; (vector-ref-bv (load id) (net-eval addr))]
      [(READ id addr)
       (let* ([mem-uf (vector-ref (load id) 0)]
              [mem-alist (vector-ref (load id) 1)]
              [eval-addr (net-eval addr)]
              [read-data (assoc-bv eval-addr mem-alist)])
         (cond [read-data (cdr read-data)]
               [else ;(printf "  READ-ASSOC: ~a not found~n" eval-addr)
                     (apply mem-uf (list eval-addr))]))]
      [(list out op) 
       (let ([result 
              (match op
                [(WRITE addr data we) 
                 (cond [(not (bvzero? (net-eval we)))
                        (let* ([mem-uf (vector-ref (load out) 0)]
                              [mem (vector-ref (load out) 1)]
                              [eval-addr (net-eval addr)]
                              [eval-data (net-eval data)]
                              [assoc-data (assoc-bv eval-addr mem)])
                          ;(printf "  WRITE-ASSOC~n  eval addr ~a~n" eval-addr)
                          ;(printf "  eval data: ~a~n" eval-data)
                          ;(printf "  assoc data: ~a~n" assoc-data)
                          (vector mem-uf
                            (cond [assoc-data
                                   (acons eval-addr eval-data (remove assoc-data mem))]
                                  [else (acons eval-addr eval-data mem)])))]
                          ;(acons eval-addr eval-data mem))]
                       [else (load out)])]
                ;[(WRITE addr data we) 
                ; (cond [(not (bvzero? (net-eval we)))
                ;        (vector-set!-bv (net-eval out) 
                ;                        (net-eval addr) 
                ;                        (net-eval data))
                ;        (net-eval out)]
                ;       [else (load out)])]
                [_ (net-eval op)])])
         (cond [(hash-has-key? regmap out) => (hash-set! regmap out result)]
               [else => (store out result)]))]))

  ; run it!
  (for ([s (block-stmts program)])
    ;(printf "net-eval: ~a~n" s)
    (net-eval s))

  (values env regmap))

(define (simulate! 
                #:sketch sketch
                #:steps steps
                #:inputs inputs)
  ; env setup
  (define-values (env regmap holemap) 
                 (setup-env sketch 0 steps inputs))
  (define ports-map (build-ports-map (block-decls sketch)))
  (define (ports name) (hash-ref ports-map name))

  (define pre-env (vector-copy env))
  (define (pre i) (vector-ref pre-env i))
  (print-env (block-decls sketch) env)

  ; evaluate 1 step
  (set!-values (env regmap) (interpret sketch
                                       env 
                                       regmap))
  ; then the rest
  (for ([i (cdr (range steps))])
    (set!-values (env regmap) (interpret sketch
                                         (update-env env (hash) regmap (hash)) 
                                         regmap))
    (print-env (block-decls sketch) env)
    )
  (set! env (update-env env (hash) regmap (hash)))
  (print-env (block-decls sketch) env))


(define (synth!-2 #:preconditions preconditions 
                #:postconditions postconditions
                #:sketch sketch
                #:steps steps
                #:reg-state reg-state
                #:mem-state mem-state
                #:inputs inputs)
  ; env setup
  (define-values (env regmap holemap) 
                 (setup-env sketch 0 steps inputs))
  (define ports-map (build-ports-map (block-decls sketch)))
  (define (ports name) (hash-ref ports-map name))

  ;; deep copy environment otherwise memory vectors will be mutated
  (define (copy-env e)
    (define new-env (vector-copy e))
    (for ([entry e]
          [index (in-naturals)])
         (cond 
           [(union? entry)
            (vector-set! new-env
                         index
                         (union-contents entry))]
           [(vector? entry)
            (vector-set! new-env
                         index
                         (vector->immutable-vector (vector-copy entry)))]))
    new-env)
  (define pre-env (copy-env env))
  (define (pre i) (vector-ref pre-env i))

  ;; thoughts about faking a kind of temporal "eventually" operator? <>
  ;; keep track of state vectors over all steps of symbolic execution,
  ;; then tell solver that at _some point_ this state assertion holds...
  ;; what does that look like?
  ;;    (assume preconditions step-0)
  ;;    (assert (or (postconditions step-1) (postconditions step-2) ...))

  (print-env (block-decls sketch) env)

  ;(for ([h holemap])
  ;     (printf "* ~a~n" h))

  ; evaluate 1 step
  (set!-values (env regmap) (interpret sketch
                                       env 
                                       regmap))
  (print-env (block-decls sketch) env)

  (define step1-env (copy-env (update-env env (hash) regmap (hash))))
  (define (step1 i) (vector-ref step1-env i))

  ; then the rest
  (for ([i (cdr (range steps))])
    ;(let ([nenv (update-env env (hash) regmap (vector-ref holemap i))])
      (set!-values (env regmap) (interpret sketch
                                           (update-env env (hash) regmap (vector-ref holemap i));nenv 
                                           regmap))
      ;)
    (print-env (block-decls sketch) env)
    )
  (set! env (update-env env (hash) regmap (hash)))

  (print-env (block-decls sketch) env)
  (print-holes (block-decls sketch) 
               holemap
               steps)
  (define (post i) (vector-ref env i))

  ;(printf "forall: ~a~n" 
  ;     (append (map pre (map ports reg-state))
  ;             (list (vector-ref (pre (ports "imem")) 0)
  ;                   (vector-ref (pre (ports "dmem")) 0))
  ;             (vector->list (pre (ports "rf")))
  ;             (filter (lambda (x) x) (vector->list (vector-ref holemap 1)))
  ;             ))


  ;; split state postconditions experiment
  (define (post-pc4 pre post ports) 
    ;(assert
      (equal? (post (ports "pc"))
              (bvadd
                (pre (ports "pc"))
                (bv 4 32))))

  (define (post-pcimm pre post ports)
    (let* (
           [ir (apply (vector-ref (pre (ports "imem")) 0)
                      (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
           [imm (sign-extend (concat
                  (bit 31 ir)
                  (bit 7 ir)
                  (extract 30 25 ir)
                  (extract 11 8 ir)
                  (bv 0 1))
                  (bitvector 32))]
           )
      (begin 
         ;(assert
           (equal? (post (ports "pc"))
                   (bvadd
                     (pre (ports "pc"))
                     imm)))))


  ; solve
  (define model
    (synthesize
     #:forall
       (append (map pre (map ports reg-state))
               (vector->list (pre (ports "rf")))
               (list (vector-ref (pre (ports "imem")) 0)
                     (vector-ref (pre (ports "dmem")) 0))
               (filter (lambda (x) x) (vector->list (vector-ref holemap 1)))
               )
     #:guarantee 
    ;(verify
       (begin
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_mem_read_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_reg_write_src_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_reg_write_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_imm_type_hole")) (bv 3 3)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_mem_sign_ext_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_branch_inv_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_mem_write_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_alu_op_hole")) (bv 4 4)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_alu_pc_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_alu_imm_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_target_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_mask_mode_hole")) (bv 0 2)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_jump_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_branch_hole")) (bv 1 1)))
         ;;; ---
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_mem_read_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_reg_write_src_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_reg_write_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_imm_type_hole")) (bv 7 3)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_mem_sign_ext_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_branch_inv_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_mem_write_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_alu_op_hole")) (bv #xf 4)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_alu_pc_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_alu_imm_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_target_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_mask_mode_hole")) (bv 0 2)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_jump_hole")) (bv 0 1)))
         ;(assume (equal? (vector-ref (vector-ref holemap 1) (ports "cont_branch_hole")) (bv 0 1)))
         (apply preconditions (list pre ports))
         (apply postconditions (list pre post ports))
         (assert
           ;(or 
           (apply post-pc4 (list pre step1 ports)))
           ;(apply post-pc4 (list pre post ports))))

         ;(assume (bvzero? (pre (ports "ex_cont_branch"))))
         ;(assume (bvzero? (pre (ports "ex_cont_jump"))))
         ;(assume (bvzero? (pre (ports "ex_cont_reg_write"))))
         ;(assume (bvzero? (post (ports "ex_cont_branch"))))
         ;(assume (bvzero? (post (ports "ex_cont_jump"))))
         ;(assume (bvzero? (post (ports "ex_cont_reg_write"))))
         ;(assume (bvzero? (pre (ports "ex_cont_mem_read"))))
         ;(assume (bvzero? (pre (ports "ex_cont_mem_write"))))
         ;(assume (not (bvzero? (pre (ports "ex_cont_valid")))))
         ;(assume (not (bvzero? (post (ports "ex_cont_valid")))))
         ;(assert (not (bvzero? (apply (vector-ref (pre (ports "imem")) 0)
         ;                                     (list (bvlshr (pre (ports "ex_pc")) (bv 2 32)))))))
         ;(assert (not (bvzero? (apply (vector-ref (pre (ports "imem")) 0)
         ;                             (list (bvlshr (pre (ports "pc")) (bv 2 32)))))))
         ;(assert (not (bvzero? (apply (vector-ref (step1 (ports "imem")) 0)
         ;                             (list (bvlshr (step1 (ports "pc")) (bv 2 32)))))))
         ;(assert (not (bvzero? (apply (vector-ref (post (ports "imem")) 0)
         ;                             (list (bvlshr (post (ports "pc")) (bv 2 32)))))))

         ;; beq spec
         ;(let* (
         ;       [ir (apply (vector-ref (pre (ports "imem")) 0)
         ;                  (list (bvlshr (pre (ports "pc")) (bv 2 32))))]
         ;       [rs1 (extract 19 15 ir)]
         ;       [rs2 (extract 24 20 ir)]
         ;       [rs1-val 
         ;            (if 
         ;              (bvzero? rs1)
         ;              (bv 0 32)
         ;              (vector-ref-bv (pre (ports "rf")) rs1))] 
         ;       [rs2-val
         ;            (if 
         ;              (bvzero? rs2)
         ;              (bv 0 32)
         ;              (vector-ref-bv (pre (ports "rf")) rs2))]
         ;       [imm (sign-extend (concat
         ;              (bit 31 ir)
         ;              (bit 7 ir)
         ;              (extract 30 25 ir)
         ;              (extract 11 8 ir)
         ;              (bv 0 1))
         ;              (bitvector 32))]
         ;       [br? (bveq rs1-val rs2-val)])
         ;  ;; note: both of these work under verification wrt reference,
         ;  ;;       but the second is slower
         ;  (assert
         ;    (equal? (if br?
         ;              (post (ports "pc"))
         ;              (step1 (ports "pc")))
         ;            (bvadd
         ;              (pre (ports "pc"))
         ;              (if br? 
         ;                imm
         ;                (bv 4 32)))))
         ;  ;(if (bveq rs1-val rs2-val)
         ;  ;    ;; eventually pc <- pc+imm
         ;  ;    (assert
         ;  ;      (or 
         ;  ;      (apply post-pcimm (list pre step1 ports))
         ;  ;      (apply post-pcimm (list pre post ports))))
         ;  ;    ;; else eventually pc <- pc+4
         ;  ;    (assert
         ;  ;      (or 
         ;  ;      (apply post-pc4 (list pre step1 ports))
         ;  ;      (apply post-pc4 (list pre post ports)))))
         ;  )
  
         )
  ))

  (cond [(unsat? model) (printf "Unsynth!~n") #f]
        [else (print-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)
              ;(let* ([pre-menv  (evaluate pre-env model)]
              ;       [step1-menv (evaluate step1-env model)]
              ;       [post-menv (evaluate env model)]
              ;       [pre-ir (apply (vector-ref (vector-ref pre-menv (ports "imem")) 0)
              ;                        (list (bvlshr (vector-ref pre-menv (ports "pc")) (bv 2 32))))]
              ;       [step1-ir (apply (vector-ref (vector-ref step1-menv (ports "imem")) 0)
              ;                        (list (bvlshr (vector-ref step1-menv (ports "pc")) (bv 2 32))))]
              ;       [post-ir (apply (vector-ref (vector-ref post-menv (ports "imem")) 0)
              ;                        (list (bvlshr (vector-ref post-menv (ports "pc")) (bv 2 32))))])
              ;  (printf "pred op ~a(~a)~n" (extract 6 0 (apply (vector-ref (vector-ref pre-menv (ports "imem")) 0)
              ;                                (list (bvlshr (vector-ref pre-menv (ports "ex_pc")) (bv 2 32)))))
              ;                             (vector-ref pre-menv (ports "ex_pc")))
              ;  (printf "pred branch: ~a~n" (vector-ref pre-menv (ports "ex_cont_branch")))
              ;  (printf "pred jump ~a~n" (vector-ref pre-menv (ports "ex_cont_jump")))
              ;  (printf "pred alu op ~a~n" (vector-ref pre-menv (ports "ex_cont_alu_op")))
              ;  (printf "pred reg write ~a~n" (vector-ref pre-menv (ports "ex_cont_reg_write")))
              ;  (printf "pred mem write ~a~n" (vector-ref pre-menv (ports "ex_cont_mem_write")))
              ;  (printf "pred mem read ~a~n" (vector-ref pre-menv (ports "ex_cont_mem_read")))
              ;  (printf "pred valid ~a~n-------~n" (vector-ref pre-menv (ports "ex_cont_valid")))
              ;  (printf "target inst op: ~a (~a)~n" (extract 6 0 pre-ir) (vector-ref pre-menv (ports "pc")))
              ;  (printf "step1 op: ~a (~a)~n" (extract 6 0 step1-ir) (vector-ref step1-menv (ports "pc")))
              ;  (printf "step1 branch: ~a~n" (vector-ref step1-menv (ports "ex_cont_branch")))
              ;  (printf "step1 jump ~a~n" (vector-ref step1-menv (ports "ex_cont_jump")))
              ;  (printf "step1 alu op ~a~n" (vector-ref step1-menv (ports "ex_cont_alu_op")))
              ;  (printf "step1 reg write ~a~n" (vector-ref step1-menv (ports "ex_cont_reg_write")))
              ;  (printf "step1 mem write ~a~n" (vector-ref step1-menv (ports "ex_cont_mem_write")))
              ;  (printf "step1 mem read ~a~n" (vector-ref step1-menv (ports "ex_cont_mem_read")))
              ;  (printf "step1 valid ~a~n-------~n" (vector-ref step1-menv (ports "ex_cont_valid")))
              ;  (printf "succ op: ~a (~a)~n" (extract 6 0 post-ir) (vector-ref post-menv (ports "pc")))
              ;  (printf "succ branch: ~a~n" (vector-ref post-menv (ports "ex_cont_branch")))
              ;  (printf "succ jump ~a~n" (vector-ref post-menv (ports "ex_cont_jump")))
              ;  (printf "succ alu op ~a~n" (vector-ref post-menv (ports "ex_cont_alu_op")))
              ;  (printf "succ reg write ~a~n" (vector-ref post-menv (ports "ex_cont_reg_write")))
              ;  (printf "succ mem write ~a~n" (vector-ref post-menv (ports "ex_cont_mem_write")))
              ;  (printf "succ mem read ~a~n" (vector-ref post-menv (ports "ex_cont_mem_read")))
              ;  (printf "succ valid ~a~n" (vector-ref post-menv (ports "ex_cont_valid")))
              ;  )
              (get-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)]))

(define (verify!-3 #:preconditions preconditions 
                #:postconditions postconditions
                #:sketch sketch
                #:steps steps
                #:reg-state reg-state
                #:mem-state mem-state
                #:inputs inputs)
  ; env setup
  (define-values (env regmap holemap) 
                 (setup-env sketch 0 steps inputs))
  (define ports-map (build-ports-map (block-decls sketch)))
  (define (ports name) (hash-ref ports-map name))

  ;; deep copy environment otherwise memory vectors will be mutated
  (define (copy-env e)
    (define new-env (vector-copy e))
    (for ([entry e]
          [index (in-naturals)])
         (cond 
           [(union? entry)
            (vector-set! new-env
                         index
                         (union-contents entry))]
           [(vector? entry)
            (vector-set! new-env
                         index
                         (vector->immutable-vector (vector-copy entry)))]))
    new-env)
  (define pre-env (copy-env env))
  (define (pre i) (vector-ref pre-env i))

  (define step-envs (make-vector steps #f))

  ;(print-env (block-decls sketch) env)

  ;(for ([h holemap])
  ;     (printf "* ~a~n" h))

  ; evaluate 1 step
  (set!-values (env regmap) (interpret sketch
                                       env 
                                       regmap))
  ;(print-env (block-decls sketch) env)

  (vector-set! step-envs 0 (vector-copy (update-env env (hash) regmap (hash))))
  ;(define if/d-env (vector-copy (update-env env (hash) regmap (hash))))
  ;(define (if/d i) (vector-ref if/d-env i))

  ; then the rest
  (for ([i (cdr (range steps))])
    (let ([nenv (update-env env (hash) regmap (vector-ref holemap i))])
      (set!-values (env regmap) (interpret sketch
                                           nenv 
                                           regmap))
      (vector-set! step-envs i (vector-copy (update-env env (hash) regmap (hash)))))
      ;)
    ;(print-env (block-decls sketch) env)
    )
  (set! env (update-env env (hash) regmap (hash)))

  ;(print-env (block-decls sketch) env)
  ;(print-holes (block-decls sketch) 
  ;             holemap
  ;             steps)
  (define (post i) (vector-ref env i))

  ;(printf "forall: ~a~n" 
  ;     (append (map pre (map ports reg-state))
  ;             (list (vector-ref (pre (ports "imem")) 0)
  ;                   (vector-ref (pre (ports "dmem")) 0)
  ;                   (vector-ref (pre (ports "rf")) 0))
  ;             ))
  ;(define (pc-state i)
  ;  (vector-ref (vector-ref step-envs (apply choose* (range steps))) i))

  ; solve
  (define model
    (synthesize
     #:forall
       (append (map pre (map ports reg-state))
               (list (vector-ref (pre (ports "imem")) 0)
                     (vector-ref (pre (ports "dmem")) 0)
                     (vector-ref (pre (ports "rf")) 0))
               )
     #:guarantee 
       (begin
         (apply preconditions (list pre ports))
         (apply postconditions (list pre step-envs ports))
         )
  ))

  (cond [(unsat? model) (printf "Unsynth!~n") #f]
        [else (print-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)
              (get-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)]))


(define (synth!-3 #:preconditions preconditions 
                #:postconditions postconditions
                #:sketch sketch
                #:steps steps
                #:reg-state reg-state
                #:mem-state mem-state
                #:inputs inputs)
  ; env setup
  (define-values (env regmap holemap) 
                 (setup-env sketch 0 steps inputs))
  (define ports-map (build-ports-map (block-decls sketch)))
  (define (ports name) (hash-ref ports-map name))

  (vector-set! env (ports "trap") (bv 1 1))

  ;; deep copy environment otherwise memory vectors will be mutated
  (define pre-env (vector-copy env))
  (for ([entry pre-env]
        [index (in-naturals)])
       (cond [(vector? entry) 
              (vector-set! pre-env
                           index
                           (vector->immutable-vector (vector-copy entry)))]))
  (define (pre i) (vector-ref pre-env i))

  ;(print-env (block-decls sketch) env)

  ;(for ([h holemap])
  ;     (printf "* ~a~n" h))

  ; evaluate 1 step
  (set!-values (env regmap) (interpret sketch
                                       env 
                                       regmap))
  ;(print-env (block-decls sketch) env)

  ;(define if/d-env (vector-copy (update-env env (hash) regmap (hash))))
  ;(define (if/d i) (vector-ref if/d-env i))

  ; then the rest
  (for ([i (cdr (range steps))])
    (let ([nenv (update-env env (hash) regmap (vector-ref holemap i))])
      (cond [(= i 1) =>
                     (vector-set! nenv (ports "trap") (bv 0 1))]
            [else =>
                     (vector-set! nenv (ports "trap") (bv 1 1))])
      (set!-values (env regmap) (interpret sketch
                                           nenv 
                                           regmap)))
      ;)
    ;(print-env (block-decls sketch) env)
    )
  (set! env (update-env env (hash) regmap (hash)))

  ;(print-env (block-decls sketch) env)
  ;(print-holes (block-decls sketch) 
  ;             holemap
  ;             steps)
  (define (post i) (vector-ref env i))

  ;(printf "forall: ~a~n" 
  ;     (append (map pre (map ports reg-state))
  ;             (list (vector-ref (pre (ports "imem")) 0)
  ;                   (vector-ref (pre (ports "dmem")) 0)
  ;                   (vector-ref (pre (ports "rf")) 0))
  ;             ))

  ; solve
  (define model
    (synthesize
     #:forall
       (append (map pre (map ports reg-state))
               ;(vector->list (pre (ports "rf")))
               (list (vector-ref (pre (ports "imem")) 0)
                     (vector-ref (pre (ports "dmem")) 0)
                     (vector-ref (pre (ports "rf")) 0))
               (vector->list (vector-ref holemap 0))
               (vector->list (vector-ref holemap 2))
               )
     #:guarantee 
       (begin
         (apply preconditions (list pre ports))

         (assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_jump_hole")) (bv 0 1)))
         (assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_branch_hole")) (bv 0 1)))

         (assume (equal? (vector-ref (vector-ref holemap 2) (ports "cont_jump_hole")) (bv 0 1)))
         (assume (equal? (vector-ref (vector-ref holemap 2) (ports "cont_branch_hole")) (bv 0 1)))

         (assume (equal? (vector-ref (vector-ref holemap 0) (ports "cont_mem_write_hole")) (bv 0 1)))
         (assume (equal? (vector-ref (vector-ref holemap 2) (ports "cont_mem_write_hole")) (bv 0 1)))

         (apply postconditions (list pre post ports))
         )
  ))

  (cond [(unsat? model) (printf "Unsynth!~n") #f]
        [else (print-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)
              (get-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)]))

(define (synth! #:preconditions preconditions 
                #:postconditions postconditions
                #:sketch sketch
                #:steps steps
                #:reg-state reg-state
                #:mem-state mem-state
                #:inputs inputs)
  ; env setup
  (define-values (env regmap holemap) 
                 (setup-env sketch 0 steps inputs))
  (define ports-map (build-ports-map (block-decls sketch)))
  (define (ports name) (hash-ref ports-map name))

  ;; deep copy environment otherwise memory vectors will be mutated
  (define pre-env (vector-copy env))
  (for ([entry pre-env]
        [index (in-naturals)])
       (cond [(vector? entry) 
              (vector-set! pre-env
                           index
                           (vector->immutable-vector (vector-copy entry)))]))
  (define (pre i) (vector-ref pre-env i))

  ; evaluate 1 step
  (set!-values (env regmap) (interpret sketch
                                       env 
                                       regmap))

  ; then the rest
  (for ([i (cdr (range steps))])
      (set!-values (env regmap) (interpret sketch
                                           (update-env env (hash) regmap (vector-ref holemap i))
                                           regmap))
    )
  (set! env (update-env env (hash) regmap (hash)))

  (define (post i) (vector-ref env i))

  ; solve
  (define model
    (synthesize
     #:forall
       (append (map pre (map ports reg-state))
               (map (lambda (m) (vector-ref (pre m) 0))
                    (map ports mem-state)))
     #:guarantee 
       (begin
         (apply preconditions (list pre ports))
         (apply postconditions (list pre post ports)))))

  (cond [(unsat? model) (printf "Unsynth!~n") #f]
        [else (print-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)
              (get-holes (block-decls sketch) 
                           (evaluate holemap model)
                           steps)]))


(define (synth-instrs! #:semantics semantics
                       #:steps steps 
                       #:sketch sketch 
                       #:reg-state regs
                       #:mem-state mems
                       [ops (list)])
  (define select-semantics
    (if (empty? ops)
        semantics
        (for/hash ([op ops])
          (values op (hash-ref semantics op)))))

  (for/hash ([(op i) select-semantics])
       (printf "~n--- ~a ---~n" op)
       (let* ([pre-i (first i)]
             [post-i (second i)]
             [hole-vals
         (synth!
           #:preconditions pre-i
           #:postconditions post-i
           #:sketch sketch
           #:steps steps
           #:reg-state regs
           #:mem-state mems 
           #:inputs (build-sym-inputs (block-decls sketch)))])
         (clear-vc!)
         (values op hole-vals))))

