(define append
	(let ((null? null?) (car car) (cdr cdr) (cons cons))
	  (lambda args
		((letrec ((f (lambda (ls args)
					   (if (null? args)
						   ls
						   ((letrec ((g (lambda (ls)
										  (if (null? ls)
											  (f (car args) (cdr args))
											  (cons (car ls) (g (cdr ls)))))))
							  g) ls)))))
		   f) '() args))))
  
  (define zero? 
	(let ((= =))
	  (lambda (x) (= x 0))))
  
  (define list (lambda x x))
  
  (define list? 
	(let ((null? null?) (pair? pair?) (cdr cdr))
	  (lambda (x)
		(or (null? x)
		(and (pair? x) (list? (cdr x)))))))
  
  (define length
	(let ((null? null?) (pair? pair?) (cdr cdr) (+ +))
	  (lambda (x)
		(letrec ((count 0) (loop (lambda (lst count)
				   (cond ((null? lst) count)
						 ((pair? lst) (loop (cdr lst) (+ 1 count)))
						 (else "this should be an error, but you don't support exceptions")))))
	  (loop x 0)))))
  
  (define make-string
	(let ((null? null?)(make-string make-string)(car car)(= =)(length length))
	  (lambda (x . y)
		(cond ((null? y) (make-string x #\nul))
		  ((= 1 (length y)) (make-string x (car y)))
		  (else "this should be an error, but you don't support exceptions")))))
  
  (define make-vector
	(let ((length length)(make-vector make-vector)(car car)(null? null?))
	  (lambda (x . y)
		(cond ((null? y) (make-vector x 0))
		  ((= 1 (length y)) (make-vector x (car y)))
		  (else "this should be an error, but you don't support exceptions")))))
  

  (define not
	(let ((eq? eq?))
	  (lambda (x)
		(if (eq? x #t) #f #t))))
  
  (define number?
	(let ((float? float?) (integer? integer?))
	  (lambda (x)
		(or (float? x) (integer? x)))))
  
  (define list->vector
	(let ((null? null?)(pair? pair?)(car car)(cdr cdr)(make-vector make-vector)(length length)(+ +))
	  (lambda (lst)
		(letrec ((loop (lambda (lst vec count)
				 (cond ((null? lst) vec)
				   ((pair? lst) (loop (cdr lst) (begin (vector-set! vec count (car lst)) vec) (+ 1 count)))
				   (else "this should be an error, but you don't support exceptions")))))
	  (loop lst (make-vector (length lst)) 0)))))
  
  (define vector->list
	(let ((< <)(vector-ref vector-ref)(cons cons)(vector-length vector-length)(- -))
	  (lambda (vec)
		(letrec ((loop (lambda (vec lst count)
				 (cond ((< count 0) lst)
				   (else (loop vec (cons (vector-ref vec count) lst) (- count 1)))))))
	  (loop vec '() (- (vector-length vec) 1))))))
  
  (define vector
	(let ((list->vector list->vector))
		(lambda x (list->vector x))))