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

  (define (unzip lst [acc '()])
    (if (or (empty? lst) (empty? (car lst)))
      (reverse acc)
      (unzip (map cdr lst) (cons (map car lst) acc))))
  (define unzipped-holes (unzip (vector->list hole-env)))

  (for ([i (range steps)])
       (vector-set! holemap i (list->vector (list-ref unzipped-holes i))))

  (for ([d (block-decls net)])
    (let ([id (first d)] [args (second d)])
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
      [(READ id addr)
       (let* ([mem-uf (vector-ref (load id) 0)]
              [mem-alist (vector-ref (load id) 1)]
              [eval-addr (net-eval addr)]
              [read-data (assoc-bv eval-addr mem-alist)])
         (cond [read-data (cdr read-data)]
               [else (apply mem-uf (list eval-addr))]))]
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
                          (vector mem-uf
                            (cond [assoc-data
                                   (acons eval-addr eval-data (remove assoc-data mem))]
                                  [else (acons eval-addr eval-data mem)])))]
                       [else (load out)])]
                [_ (net-eval op)])])
         (cond [(hash-has-key? regmap out) => (hash-set! regmap out result)]
               [else => (store out result)]))]))

  ; run it!
  (for ([s (block-stmts program)])
    (net-eval s))

  (values env regmap))

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
