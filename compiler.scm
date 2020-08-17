;;;;
;; Datatypes
;;;;

(define (expr-mask expr-shift)
  (- (ash 1 expr-shift) 1))

(define fixnum-shift 2)
(define fixnum-mask (expr-mask fixnum-shift))

(define ptr-mask 7) ; mask for pointer type tag
(define ptr-mask-inv #xfffffff8) ; mask for pointer value

(define pair-tag 1)
(define vec-tag 2)
(define str-tag 3)
(define sym-tag 5)
(define closure-tag 6)

(define char-shift 8)
(define char-mask (expr-mask char-shift)) ; character type mask
(define char-tag 7)

(define bool-shift 8)
(define bool-mask (expr-mask bool-shift))
(define bool-tag 15)

;;;;
;; Helpers
;;;;

(define (not-null? x) (not (null? x)))

(define (eval-shift x offset)
  (if (<= x 1) offset (eval-shift (/ x 2) (+ offset 1))))

(define (remove-list-duplicates! x)
  (if (null? x) x
      (cons (car x) (remove-list-duplicates! (delq (car x) x)))))

;;;;
;; Stack
;;;;

(define wordsize 4)

(define word-shift (eval-shift wordsize 0))

;;;;
;; Immediates
;;;;

(define (immediate? x)
  (or (integer? x) (char? x) (boolean? x) (null? x)))

(define (immediate-rep x)
  (cond ((integer? x) (logand (ash x fixnum-shift) #xffffffff))
        ((char? x) (logior (ash (char->integer x) char-shift) char-tag))
        ((boolean? x)
         (if x
             (logior (ash 1 bool-shift) bool-tag)
             bool-tag))
        ((null? x) pair-tag)
        ))

;;;;
;; Primitive Calls
;;;;

; Check whether the passed form is a primitive call (primcall) form
(define (primitive-call? form) (eq? 'primcall (car form)))

; Get the primitive operation from a passed primcall form
(define (primitive-op form) (cadr form))

; Get the Nth argument of a passed primcall form
(define (primitive-op-arg form index) (list-ref form (+ index 1)))

; Get all arguments of a passed primcall form
(define (primitive-op-args form) (cddr form))

(define (compile-primitive-call form si env)
  (case (primitive-op form)
    ((add1)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "addl $~a, %eax" (immediate-rep 1)))
    ((sub1)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "subl $~a, %eax" (immediate-rep 1)))
    ((integer?)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "andl $~a, %eax" fixnum-mask)
     (emit-is-eax-equal-to 0))
    ((char?)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "andl $~a, %eax" char-mask)
     (emit-is-eax-equal-to char-tag))
    ((boolean?)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "andl $~a, %eax" bool-mask)
     (emit-is-eax-equal-to bool-tag))
    ((zero?)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit-is-eax-equal-to 0))
    ((not)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit-is-eax-equal-to bool-tag))
    ((integer->char)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "sall $~a, %eax" (- char-shift fixnum-shift))
     (emit "orl $~a, %eax" char-tag))
    ((char->integer)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "sarl $~a, %eax" (- char-shift fixnum-shift)))
    ((+)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "addl ~a(%esp), %eax" si))
    ((-)
     (compile-expr (primitive-op-arg form 2) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 1) (- si wordsize) env)
     (emit "subl ~a(%esp), %eax" si))
    ((*)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "imull ~a(%esp), %eax" si))
    ((=)
     (emit "sarl $~a, %eax" fixnum-shift)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "cmpl %eax, ~a(%esp)" si)
     (emit "movl $0, %eax")
     (emit "sete %al")
     (emit "sall $~a, %eax" bool-shift)
     (emit "orl $~a, %eax" bool-tag))
    ((<)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "cmpl %eax, ~a(%esp)" si)
     (emit "movl $0, %eax")
     (emit "setl %al")
     (emit "sall $~a, %eax" bool-shift)
     (emit "orl $~a, %eax" bool-tag))
    ((char=?)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "sarl $~a, %eax" char-shift)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "sarl $~a, %eax" char-shift)
     (emit "cmpl %eax, ~a(%esp)" si)
     (emit "movl $0, %eax")
     (emit "sete %al")
     (emit "sall $~a, %eax" bool-shift)
     (emit "orl $~a, %eax" bool-tag))
    ((cons)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "movl %eax, ~a(%esi)" wordsize)
     (emit "movl ~a(%esp), %eax" si)
     (emit "movl %eax, 0(%esi)")
     (emit "movl %esi, %eax")
     (emit "orl $~a, %eax" pair-tag)
     (emit "addl $~a, %esi" (* wordsize 2)))
    ((null?)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit-is-eax-equal-to pair-tag))
    ((car)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl ~a(%eax), %eax" (- pair-tag)))
    ((cdr)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl ~a(%eax), %eax" (- 4 pair-tag)))
    ((set-car!)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "movl ~a(%esp), %edx" si)
     (emit "movl %eax, ~a(%edx)" (- pair-tag)))
    ((set-cdr!)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "movl %eax, ~a(%esp)" si)
     (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
     (emit "movl ~a(%esp), %edx" si)
     (emit "movl %eax, ~a(%edx)" (- 4 pair-tag)))
    ((make-string)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "shrl $~a, %eax" fixnum-shift)
     (emit "movl %eax, 0(%esi)")
     (emit "movl %eax, %ecx")
     (emit "movl %esi, %eax")
     (emit "orl $~a, %eax" str-tag)
     (emit "addl $11, %ecx") ;; move to next double-word, length (4) + 11 = 15
     (emit "andl $-8, %ecx") ;; 8-bit boundary
     (emit "addl %ecx, %esi")
     (if (not-null? (cdddr form))
         (begin
           (emit "movl %eax, ~a(%esp)" si)
           (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
           (emit "shrl $~a, %eax" char-shift)
           (emit "movl ~a(%esp), %edi" si)
           (emit "subl $~a, %edi" str-tag)
           (emit "movl 0(%edi), %ecx")
           (emit "addl $~a, %edi" wordsize)
           (emit "rep stosb")
           (emit "movl ~a(%esp), %eax" si))))
    ((make-vector)
     (compile-expr (primitive-op-arg form 1) si env)
     (emit "shrl $~a, %eax" fixnum-shift)
     (emit "movl %eax, 0(%esi)")
     (emit "movl %eax, %ecx")
     (emit "sall $~a, %ecx" word-shift) ;; multiply by wordsize
     (emit "movl %esi, %eax")
     (emit "orl $~a, %eax" vec-tag)
     (emit "addl $11, %ecx") ;; move to next double-word, length (4) + 11 = 15
     (emit "andl $-8, %ecx") ;; 8-bit boundary
     (emit "addl %ecx, %esi")
     (if (not-null? (cdddr form))
         (begin
           (emit "movl %eax, ~a(%esp)" si)
           (compile-expr (primitive-op-arg form 2) (- si wordsize) env)
           (emit "movl ~a(%esp), %edi" si)
           (emit "subl $~a, %edi" vec-tag)
           (emit "movl 0(%edi), %ecx")
           (emit "addl $~a, %edi" wordsize)
           (emit "rep stosl")
           (emit "movl ~a(%esp), %eax" si))))))

;; TODO string and vector functions.

;;;;
;; Local Variables
;;;;

; Check whether the passed argument is a let call
(define (let? x) (eq? (car x) 'let))

; Check whether the passed argument is a scheme variable
(define (variable? x) (symbol? x))

(define (compile-var e si env)
  (emit "movl ~a(%esp), %eax" (cdr (assoc e env))))

(define (range a b)
  (if (= a b) '()
      (cons a (range (+ 1 a) b))))

(define (compile-let bindings body si env)
  ;; stack-offsets (list) : offset for each binding according to wordsize on the stack relative to current si
  ;; names (list) : name of each binding
  ;; exprs (list) : expression or value for each binding
  ;; inner-si : si after all the stack-offsets are added
  ;; inner-env (list) : env value after appending previous env and (name stack-offset) pairs
  (let* ((stack-offsets (map (lambda (x) (- si (* x wordsize))) (range 0 (length bindings))))
         (names (map car bindings))
         (exprs (map cadr bindings))
         (inner-si (- si (* (length bindings) wordsize)))
         (inner-env (append (map cons names stack-offsets) env)))
    ;; push each expression on it's stack offset
    (for-each (lambda (expr offset)
                (compile-expr expr inner-si env)
                (emit "movl %eax, ~a(%esp)" offset))
              exprs stack-offsets)
    (for-each (lambda (form)
                (compile-expr form inner-si inner-env))
              body)))

;;;;
;; Conditionals
;;;;

; Check wheter the passed argument is a if call
(define (if? x) (eq? (car x) 'if))

(define current-label 0)

(define (unique-label)
  (let ((label current-label))
    (set! current-label (+ 1 label))
    (format #f "label_~a" label)))

(define (compile-if cond exec-true exec-false si env)
  (let ((false-label (unique-label))
        (end-label (unique-label)))
    (compile-expr cond si env)
    (emit "cmpl $~a, %eax" (immediate-rep #f))
    (emit "je ~a" false-label)
    (compile-expr exec-true si env)
    (emit "jmp ~a" end-label)
    (emit "~a:" false-label)
    (compile-expr exec-false si env)
    (emit "~a:" end-label)))

;;;;
;; Function Calls
;;;;

; Check wheter the passed argument is a lambda call
(define (lambda? x) (eq? (car x) 'lambda))

(define (x-form-annotate-free-vars e env)
  (cond
  ;; <Expr>
  ((null? e) (list e '()))
  ;; <Expr>
  ((variable? e)
   (list e (if (member e env) '() (list e))))
  ;; <Expr>
  ((not (list? e)) (list e '()))
  ;; (if <Expr> <Expr> <Expr>)
  ((if? e)
   (let* ((parts (map (lambda (x) (x-form-annotate-free-vars x env)) (cdr e)))
          (annotated (map car parts))
          (free-variables (map cadr parts)))
     (list `(if ,@annotated)
           (remove-list-duplicates! (apply append free-variables)))))
  ;; (lambda args free-variables <Expr>...)
  ((lambda? e)
   (let* ((lambda-args (cadr e))
          (lambda-body (caddr e))
          (annotated-body (x-form-annotate-free-vars lambda-body env))
          ;; free variables from lambda-body, exclude lambda-args
          (free-variables (filter (lambda (x) (not (memq x lambda-args))) (cadr annotated-body))))
     ;;outgoing free vars shouldn't include parts of our input env
     (list `(lambda ,lambda-args ,free-variables ,(car annotated-body))
           (filter (lambda (v) (not (memq v env))) free-variables))))
  ;; (primcall prim-name <Expr>...)
  ((primitive-call? e)
   (let* ((results (map (lambda (x) (x-form-annotate-free-vars x env)) (cddr e)))
          (annotated (map car results))
          (free-variables (apply append (map cadr results))))
     (list `(primcall ,(cadr e) ,@annotated)
           (remove-list-duplicates! free-variables))))
  ;; (let (lvar <Expr> ...) <Expr>)
  ((let? e)
   (let* ((bindings (cadr e))
          (let-body (cddr e))
          (let-variables (map car bindings))
          (let-exprs (map cadr bindings))
          (annotated-exprs (map (lambda (x) (x-form-annotate-free-vars x env)) let-exprs))
          (expr-bodies (map car annotated-exprs))
          (expr-free (apply append (map cadr annotated-exprs)))
          (inner-env (append let-variables env))
          (inner-annotated (map (lambda (x) (x-form-annotate-free-vars x inner-env)) let-body)))
     (list `(let ,(map list let-variables expr-bodies) ,@(map car inner-annotated))
           (remove-list-duplicates! (append expr-free (apply append (map cadr inner-annotated)))))))
  (else (let* ((results (map (lambda (p) (x-form-annotate-free-vars p env)) e))
               (annotated (map car results))
               (free-variables (apply append (map cadr results))))
          (list annotated (remove-list-duplicates! free-variables))))
  ))


;;;;
;; Compiler
;;;;

(define emit (lambda args (apply simple-format #t args)
                     (newline)))

(define (emit-is-eax-equal-to val)
  (emit "cmpl $~a, %eax" val)
  (emit "movl $0, %eax")
  (emit "sete %al")
  (emit "sall $~a, %eax" bool-shift)
  (emit "orl $~a, %eax" bool-tag))

(define (compile-expr e si env)
  (cond
   ((immediate? e) (emit "movl $~a, %eax" (immediate-rep e)))
   ((variable? e) (compile-var e si env))
   ((let? e) (compile-let (cadr e) (cddr e) si env))
   ((if? e) (compile-if (cadr e) (caddr e) (if (null? (cdddr e)) #f (cadddr e)) si env))
   ((primitive-call? e) (compile-primitive-call e si env))))

(define (compile-program program)
  (emit ".text")
  (emit ".p2align 4,,15")
  (emit ".globl scheme_entry")
  (emit "scheme_entry:")

  ; handle incoming call from C
  (emit "push %esi")
  (emit "push %edi")
  (emit "push %edx")

  ; our code goes here
  (set! current-label 0)

  ; fetch heap pointer into %esi by accessing the heap pointer, stored 16 bytes (return address + 3 words for saved registers) before the stack pointer
  (emit "movl 16(%esp), %esi")

  (compile-expr program (- wordsize) '())

  ; restore state for return to C
  (emit "pop %edx")
  (emit "pop %edi")
  (emit "pop %esi")
  (emit "ret"))

(define (compile-to-binary program)
  (begin
    (with-output-to-file "/tmp/compiled.s"
      (lambda () (compile-program program)))
    (system "gcc -fomit-frame-pointer -m32 /tmp/compiled.s rts.c")))

(define (compile-and-run program)
  (begin (compile-to-binary program)
         (system "./a.out")))
