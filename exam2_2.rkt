#lang racket
(require csc151)
(require plot)
(require rackunit)
(require rackunit/text-ui)

;;; File:
;;;   000000.rkt
;;; Authors:
;;;   The student currently referred to as 000000
;;;   Titus Klinge
;;;   Samuel A. Rebelsky
;;; Contents:
;;;   Code and solutions for Exam 2 2018S
;;; Citations:
;;;

;; +---------+--------------------------------------------------------
;; | Grading |
;; +---------+

;; This section is for the grader's use.

;; Problem 1: 
;; Problem 2:
;; Problem 3:
;; Problem 4:
;; Problem 5:
;; Problem 6:
;;           ----
;;     Total:

;;    Scaled:
;;    Errors:
;;     Times:
;;          :
;;          :
;;          :
;;           ----
;;     Total:

;; +----------+-------------------------------------------------------
;; | Prologue |
;; +----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity

; Time Spent: 

;; +-----------+------------------------------------------------------
;; | Problem 1 |
;; +-----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity
;   2/28        11:20   11:47   Got the even list but need to think about the negative number
;   3/1         7:35    8:11    found bugs and try to fix it
;   3/3         12:30   12:57   Fixed some bugs and finished everything
; Time Spent: 

; Citations:

; Solution:

;;; Procedure:
;;;   evens-between
;;; Parameters:
;;;   start, a number
;;;   finish, an integer 
;;; Purpose:
;;;   To get even numbers between start and finish
;;; Produces:
;;;   A list of numbers
;;; Preconditions:
;;;   start cannot be an inexact number
;;; Postconditions:
;;; when start is not inexact number
;;; iota will take in the number and make a list of number
;;; then will filter out all the even numbers
;;; and will drop numbers behind
;;; if the start is a negative number then
;;; get-even-negative will create a list of negative numbers
;;; then append to the postive list

;;b;;

;; Procedure:
;;;   make-negative
;;; Parameters:
;;;   number, a number
;;;   finish, an integer 
;;; Purpose:
;;;   get a list of negative number
;;; Produces:
;;;   A list of numbers
(define make-negative
  (lambda (number)
    (map * (iota (+(* -1 number) 1)))))

;; Procedure:
;;;   get-even-negative
;;; Parameters:
;;;   start, a number
;;;   finish, an integer 
;;; Purpose:
;;;   get a list of even negative number
;;; Produces:
;;;   A list of numbers
(define get-even-negative
  (lambda (start)
    (drop (filter even? (map * (make-negative start) (make-list (length (make-negative start)) -1) )) (-(* start -1) (- (* start -1)1))) ))

;;; Procedure:
;;;   get-even-negative
;;; Parameters:
;;;   start, a number
;;;   finish, an integer 
;;; Purpose:
;;;   get a list of even negative number
;;; Produces:
;;;   A list of numbers
(define get-postive-list
  (lambda (finish)
    (filter even? (iota (+ finish 1)))))
;;; Procedure:
;;;   get-between
;;; Parameters:
;;;   start, a number
;;;   finish, an integer 
;;; Purpose:
;;;   get a list of even between two bounds
;;; Produces:
;;;   A list of numbers
(define get-between
  (lambda (start finish)
    (filter even? (drop(iota (+ (* finish -1) 1))(- (* start -1)1)))))

(define evens-between-kernel
  (lambda (start finish)
    (cond
      [(and (inexact? finish) (equal? start 0))
       (get-postive-list (inexact->exact (floor finish))) ]
      [(and (negative? start) (negative? finish))
       ( map * (make-list (length (get-between start finish)) -1 )(get-between start finish))]
      [(inexact? finish)
       (drop(get-postive-list (inexact->exact (floor finish))) (- start 1))]
      [(> start 0)
       (filter even? (drop(iota (+ finish 1))(- start 1)))]
      [(< start 0)
       (append (get-even-negative start) (get-postive-list finish))]
      [else
       (filter even? (iota (+ finish 1)))])))
;;c;;
(define evens-between
  (lambda (start finish)
    (cond
      [(and (string? start) (string? finish))
       (error "Input cannot be a string")]
      
      [(string? start)
       (error "Input cannot be a string")]
     
      [(string? finish)
       (error "Input cannot be a string")]
      
      [(inexact? start)
       (error "The lower bound is not exact.")]
     
      [(evens-between-kernel start finish)]
      )))

; Examples/Tests:
#|
> (evens-between 1.0 10)
 Error: The lower bound is not exact.

> (evens-between 1.0 5)
Error: The lower bound is not exact
.
> (evens-between "a" 5)
Error: Input cannot be a string

> (evens-between 1 "a")
Error: Input cannot be a string

> (evens-between 0 10)
'(0 2 4 6 8 10)

> (evens-between 3 7.5)
'(4 6)

> (evens-between -2 5)
'(-2 0 2 4)
>
> (evens-between -4 -9)
'(-4 -6 -8)
>
> (evens-between 4 9)
'(4 6 8)
> (evens-between 5 9)
'(4 6 8)
> 
> 
|#
;; +-----------+------------------------------------------------------
;; | Problem 2 |
;; +-----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity
;   3/1         8:12    8:40    writing the test then debug the code above
; Time Spent: 

; Citations:

; Solution:

(define tests-evens-between
  (let ([check-error
         (lambda (proc)
           (check-exn (conjoin exn:fail? (negate exn:fail:contract?))
                      proc))])
    (test-suite
     "Tests of the evens-between procedure"
     (test-case
      "Lower and upper are both even"
      (check-equal? (evens-between 0 10)
                    '(0 2 4 6 8 10)))
     (test-case
      "Lower and upper are both even"
      (check-equal? (evens-between -3 -6)
                    '(-4 -6)))
     (test-case
      "upper bound inexact"
      (check-equal? (evens-between 3 7.5)
                    '(4 6)))

     (test-case
      "negative number lower bound"
      (check-equal? (evens-between -2 5)
                    '(-2 0 2 4)))
     
     (test-case
      "Preconditions are not met"
      (check-error (lambda () (evens-between "a" 1))))

     (test-case
      "Preconditions are not met"
      (check-error (lambda () (evens-between 1 "a"))))

     (test-case
      "Preconditions are not met"
      (check-error (lambda () (evens-between 50 100))))
     
     (test-case
      "Preconditions are not met"
      (check-error (lambda () (evens-between "a" "b")))))))

; Examples/Tests:


;; +-----------+------------------------------------------------------
;; | Problem 3 |
;; +-----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity
;   3/4         10:00   12:00
; Time Spent: 

; Citations:

; Solution:
(define grinco-2018S (read-csv-file "grinco-2018S.csv"))

;;; Procedure
;;;   strip
;;; Parameters
;;;   lst, a list
;;; Purpose
;;;  Take out the duplicate 
;;; Produces
;;;  A list of string or number 
(define strip
  (lambda (lst)
        (let ((first (car lst)))
          (let get ((known first)
                     (rest (cdr lst))
                     (so-far (list first)))
            (if (null? rest)
                (reverse so-far)
                (let ((first-remaining (car rest)))
                  (get first-remaining
                        (cdr rest)
                        (if (equal? known first-remaining)
                            so-far
                            (cons first-remaining so-far)))))))
        ))
;;; Procedure
;;;   get-column
;;; Parameters
;;;   table, a list of list, column, a number
;;; Purpose
;;;  take out the wanted column 
;;; Produces
;;;  A list of string or number
(define get-column
  (lambda (table column)
    (cond
      [(equal? 0 column)(map car table)]
      [(equal? 1 column)(map cadr table)]
      [(equal? 2 column)(map caddr table)]
      [(equal? 3 column)(map cadddr table)]
      [(equal? 4 column)(map caddr(map cdr table ))]
      [(equal? 5 column)(map caddr(map cddr table ))]
      [(equal? 6 column)(map cadddr(map cdddr(map cdddr table)))
                        [(equal? 7 column)(map cadddr(map cddddr table))]
                        [(equal? 8 column)(map cadddr(map cddddr (map cdr table)))]
  
                        ])))
;;; Procedure:
;;;   extract-unique
;;; Parameters:
;;;   table, a list of lists
;;;   column, a non-negative integer
;;; Purpose:
;;;   Extract the unique values in the given column of the table.
;;; Produces:
;;;   unique, a list
;;; Preconditions:
;;;   * column names a valid column in each entry of table.  That is,
;;;     `(< column (reduce min (map length table)))`
;;; Postconditions:
;;;   * Every element of the given column of table appears in unique.
;;;   * No value appears twice in unique
;;;   * Every element in unique appears in the given column of table
(define extract-unique
  (lambda (table column)
    (strip(get-column table column))
    ))


  





; Examples/Tests:
#|
(extract-unique grinco-2018S 1)
'("ALS"
  "AMS"
  "ANT"
  "ARB"
  "ARH"
  "ART"
  "BCM"
  "BIO"
  "CHI"
  "CHM"
  "CLS"
  "CSC"
  "EAS"
  "ECN"
  "EDU"
  "ENG"
  "ENV"
  "FRN"
  "GDS"
  "GEN"
  "GLS"
  "GRE"
  "GRM"
  "GWS"
  "HIS"
  "HUM"
  "ICS"
  "IPH"
  "JPN"
  "LAS"
  "LAT"
  "LIN"
  "MAT"
  "MUS"
  "NRS"
  "PCS"
  "PHE"
  "PHI"
  "PHY"
  "POL"
  "PST"
  "PSY"
  "RED"
  "REL"
  "RES"
  "RUS"
  "SCI"
  "SOC"
  "SPN"
  "SST"
  "TEC"
  "THD"
  "THS"
  "WRT")

(strip '(1 1 2 2 3 4 5))
'(1 2 3 4 5)
|#

;; +-----------+------------------------------------------------------
;; | Problem 4 |
;; +-----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity
;   3/2         12:55    2:00
;   3/4         9:30     10:00
;   3/6         9:45     10:00
; Time Spent: 

; Citations:

; Solution:

;;; Procedure:
;;;   describe-file
;;; Parameters:
;;;   fname, a string
;;; Purpose:
;;;   Provide some text to describe a file
;;; Produces:
;;;   description, a string
;;; Preconditions:
;;;   fname names an existing text file for which we have read permission.
;;; Postconditions:
;;;   * If the file contains no characters, description is "empty".
;;;   * If the file contains fewer than 1000 words, description
;;;     begins with the phrase "a short file".
;;;   * If the file contains at least 1000 words but fewer than 10,000, 
;;;     description begins with the phrase "a medium-length file".
;;;   * If the file contains at least 10,000 words but fewer than 100,000, the
;;;     description begins with the phrase "a large file".
;;;   * If the file contains at least 100,000 words, the description 
;;;     begins with the phrase "a very large file".
;;;   * If the average line length is less than twenty characters,
;;;     description includes the phrase "containing mostly short lines".
;;;   * If at least 1/3 of the words in the file are under five characters,
;;;     the description include the phrase "with many short words".
;;;   * If at least 1/3 of the words in the file are over eight characters,
;;;     the description includes the phrase "with many long words".
;;;   * If any of condition above is not met, description does not include 
;;;     the corresponding phrase.

(define long (read-csv-file "/home/rebelsky/share/files/long-short.txt"))
(define large (read-csv-file "/home/rebelsky/share/files/five-syllables.txt"))
(define empty (read-csv-file "/home/rebelsky/share/files/empty.txt"))

(define test
'("once upon a time in a land far far away"
  "there lived an engineered, exhausting, triskaidecaphobic,"
  "electronic, educational, elephantine, incredible, but nontheless"
  "understanding, monster."))


;;; Procedure:
;;;   get-average
;;; Parameters:
;;;   fname, a string
;;; Purpose:
;;;   get the average words
;;; Produces:
;;;   a number 
(define get-average
  (lambda(fname)
    (/ (reduce +(map string-length(map string-append(file->lines fname)))) (length(file->lines fname)))))
;;; Procedure:
;;;   get-under-5?
;;; Parameters:
;;;   str, a string
;;; Purpose:
;;;  check whether the string is under 5 
;;; Produces:
;;;   boolean T or F
(define get-under-5?
  (lambda (str)
    (> 5 (string-length str))
  ))
;;; Procedure:
;;;   get-over-8?
;;; Parameters:
;;;   str, a string
;;; Purpose:
;;;  check whether the string is over 8
;;; Produces:
;;;   boolean T or F
(define get-over-8?
  (lambda (str)
    (< 8 (string-length str))
  ))
;;; Procedure:
;;;   char-under-5
;;; Parameters:
;;;   fname, a string
;;; Purpose:
;;;  get the proportion of the filtered word length and the orginal length
;;; Produces:
;;;   a number
(define char-under-5
  (lambda(fname)
    (/ (length(filter get-under-5? (file->words fname))) (length (file->words fname)))
    ))
;;; Procedure:
;;;   char-over-8
;;; Parameters:
;;;   fname, a string
;;; Purpose:
;;;  get the proportion of the filtered word length and the orginal length
;;; Produces:
;;;   a number
(define char-over-8
  (lambda(fname)
    (/ (length(filter get-over-8? (file->words fname))) (length (file->words fname)))
    ))

(define describe-file
  (lambda (fname)
    (cond [(empty?(file->lines fname))
           'empty]
          [(= (length(file->lines fname)) 1000)
           "a short file"]
          [(and(>= (length(file->lines fname)) 1000) (< (length(file->lines fname)) 10000))
           "a medium-length file"]
          [(and(>= (length(file->lines fname)) 10000) (< (length(file->lines fname)) 100000))
           "a large file"]          
          [(>= (length(file->lines fname)) 100000)
           "a very large file"]
          [(< (get-average fname)20)
           "containing mostly short lines"]
          [(> (char-under-5 fname) (/ 1 3))
           "with many short words"]
          [(> (char-over-8 fname) (/ 1 3))
           "with many short words"]
          
            
          ))) 
;; +-----------+------------------------------------------------------
;; | Problem 5 |
;; +-----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity
;   3/4         7:30    9:55    stuck on b
;   3/5         2:30    4:14    asking questions and fixed everything
; Time Spent: 

; Citations:
; Assignement 5
; Solution:

; x-axis represents the number of words in a speech
; y-axis represents the average word length in the speech
(define some-speeches
  (list (list "Joe" "My name is Joe")
        (list "Jane" "I heard that Abraham Lincoln once said that ...")
        (list "Joe" "My name is still Joe")
        (list "Jae" "I am not inclined to speak at length, nor on matters ...")
        (list "Joe" "It's still Joe")
        (list "Jo" "I am often mistaken for another person. Let me explain ...")
        (list "Joe" "I'm not Jo")
        ))
;;; Procedure
;;;   remove-not-alp-smush
;;; Parameters
;;;   str, a string
;;; Purpose
;;;  to remove all characters that are non-alphabetic (including spaces)
;;; Produces
;;;   alp-str-smush, a string
(define remove-not-alp
  (lambda (str)
    (list->string (filter (disjoin (section equal? <> #\space)
                                   char-alphabetic?)
                          (string->list str)))))
;;; Procedure
;;;   string->words
;;; Parameters
;;;   str, a string
;;; Purpose
;;;   To create a list of strings
;;;   made up of all of the words in str
;;; Produces
;;;  word-lst, a list of strings
(define string->words
  (lambda (str)
    (string-split (string-downcase (remove-not-alp str)) " ")
    ))
;;; Procedure
;;;   remove-not-alp-smush
;;; Parameters
;;;   str, a string
;;; Purpose
;;;   to remove all characters that are non-alphabetic (including spaces)
;;; Produces
;;;   alp-str-smush, a string
(define remove-not-alp-smush
  (lambda (str)
    (list->string (filter char-alphabetic?
                          (string->list str)))))
;;; Procedure
;;;   cons-w/-null
;;; Parameters
;;;   num, a number OR any other input cons takes
;;; Purpose
;;;   to create a new list with num
;;; Produces
;;;   new-lst, a list containing num
(define cons-w/-null (section cons <> null))
;;; Procedure
;;;   tally-Candidate
;;; Parameters
;;;   table, a table in correct debate transcript form
;;;   candidate, a string
;;; Purpose
;;;   to calculate the number of words associated with candidate
;;; Produces
;;;   num-words, a number
(define tally-Candidate
  (lambda (table candidate)
    (reduce + (map length
                   (map string->words
                        (map cadr (take-all-Candidate table candidate)))))))
;;; Procedure
;;;   take-all-Candidate
;;; Parameters
;;;   table, a table in correct
;;; Purpose
;;;   to remove all characters that are non-alphabetic
;;;   and also not spaces in a string
;;; Produces
;;;   alp-str, a string
(define take-all-Candidate
  (lambda (table candidate)
    (filter (o (section equal? <> candidate) car) table)
    ))


;;; Procedure
;;;   total-words-list
;;; Parameters
;;;   table, a table in correct debate transcript form
;;; Purpose
;;;   to calculate the number of words associated with each candidate in table
;;; Produces
;;;   num-words-lst, a list of numbers 
(define total-words-list
  (lambda (table)
    (map  tally-Candidate (make-list (length (tally-all (map car some-speeches)))table)
          (map car (tally-all (map car some-speeches)))
         
          )))




;;; Procedure
;;;   total-words-by-candidate
;;; Parameters
;;;   table, a list of lists
;;; Purpose
;;;   to tally the number of words each candidate used
;;;   in the debate given by table
;;; Produces
;;;   tally-words, a two-column table (list of lists)
(define total-words-by-candidate
  (lambda (table)
    (map cons (map car (tally-all (map car table)))
         (map cons-w/-null (total-words-list table)))))


;;; Procedure
;;;   average-word-length-one-cand
;;; Parameters
;;;  candidate, a string, table, a list of lists
;;; Purpose
;;;   takes all the string and find the average word length
;;; Produces
;;;   an average word length number
(define average-word-length-one-cand
  (lambda (table candidate)
    (exact->inexact (/ (string-length
                        (reduce string-append
                                (map remove-not-alp-smush
                                     (map cadr
                                          (take-all-Candidate table
                                                              candidate)))))
                       (tally-Candidate table candidate)))))

;;; Procedure
;;;   total-char/word-list
;;; Parameters
;;;  table, a list of lists
;;; Purpose
;;;   takes in all the string for each indvidual candidate and get their
;;;   average word length
;;; Produces
;;;  a list of numbers    
(define total-char/word-list
  (lambda (table)
    (map average-word-length-one-cand
         (make-list (length (tally-all (map car some-speeches)))
                    table)
         (map car (tally-all (map car some-speeches))))))
;;; Procedure
;;;   average-word-length-by-candidate
;;; Parameters
;;;   table, a list of lists
;;; Purpose
;;;   Give all the candidates with the average word
;;;   length for each candidate
;;; Produces
;;;  A list of a list ofcandidate,a string, with their
;;;  averge length words, a number 
(define average-word-length-by-candidate

  (lambda (table)
    (map cons (map car (tally-all (map car table)))
         (map cons-w/-null (total-char/word-list table)))))







(define visualize-speeches
  (lambda (speeches)
    (plot (points (list (list (car(total-words-list speeches))
                              (car(total-char/word-list speeches)))
                                  
                        (list (cadr(total-words-list speeches))
                              (cadr(total-char/word-list speeches)))
                              
                        (list (caddr(total-words-list speeches))
                              (caddr(total-char/word-list speeches)))

                        (list(cadddr(total-words-list speeches))
                             (cadddr(total-char/word-list speeches))))
                  #:x-min 7
                  #:x-max 20
                  #:y-min 2
                  #:y-max 10)
          #:title "Speech"
          #:x-label "number of words in a speech "
          #:y-label "average word length in the speech")
    ))
;;b;;


(define visualize-speeches-prime
  (lambda (speeches speakers colors)
    (cond
      [(equal? speakers "Joe")
       (plot (list
              (points(list
                      (list(car(total-words-list speeches))
                           (car(total-char/word-list speeches))))
                     #:fill-color colors
                     #:sym 'fullcircle6
                     )
              (points(list         
                      (list (cadr(total-words-list speeches))
                            (cadr(total-char/word-list speeches)))
                              
                      (list (caddr(total-words-list speeches))
                            (caddr(total-char/word-list speeches)))

                      (list(cadddr(total-words-list speeches))
                           (cadddr(total-char/word-list speeches))))
                     ;#:title "Speech"
                     ;#:x-label "number of words in a speech "
                     ;#:y-label "average word length in the speech")
                     ))
             #:x-min 7
             #:x-max 20
             #:y-min 2
             #:y-max 10                 
             
             )]

      [(equal? speakers "Jane")
       (plot (list
              (points(list
                      (list (cadr(total-words-list speeches))
                            (cadr(total-char/word-list speeches))))
                     #:fill-color colors
                     #:sym 'fullcircle6
                     )
              (points(list  (list(car(total-words-list speeches))
                                 (car(total-char/word-list speeches)))         
                                                    
                            (list (caddr(total-words-list speeches))
                                  (caddr(total-char/word-list speeches)))

                            (list(cadddr(total-words-list speeches))
                                 (cadddr(total-char/word-list speeches))))
                     ;#:title "Speech"
                     ;#:x-label "number of words in a speech "
                     ;#:y-label "average word length in the speech")
                     ))
             #:x-min 7
             #:x-max 20
             #:y-min 2
             #:y-max 10                 
             
             )]

      [(equal? speakers "Jae")
       (plot (list
              (points(list
                      (list (caddr(total-words-list speeches))
                            (caddr(total-char/word-list speeches))))
                     #:fill-color colors
                     #:sym 'fullcircle6
                     )
              (points(list  (list(car(total-words-list speeches))
                                 (car(total-char/word-list speeches)))         
                            (list (cadr(total-words-list speeches))
                                  (cadr(total-char/word-list speeches)))
 
                            (list(cadddr(total-words-list speeches))
                                 (cadddr(total-char/word-list speeches))))
                     ;#:title "Speech"
                     ;#:x-label "number of words in a speech "
                     ;#:y-label "average word length in the speech")
                     ))
             #:x-min 7
             #:x-max 20
             #:y-min 2
             #:y-max 10                 
             
             )]
      [(equal? speakers "Jo")
       (plot (list
              (points(list
                      (list(cadddr(total-words-list speeches))
                           (cadddr(total-char/word-list speeches))))
                     #:fill-color colors
                     #:sym 'fullcircle6
                     )
              (points(list  (list(car(total-words-list speeches))
                                 (car(total-char/word-list speeches)))
                            
                            (list (cadr(total-words-list speeches))
                                  (cadr(total-char/word-list speeches)))
                          
                            (list (caddr(total-words-list speeches))
                                  (caddr(total-char/word-list speeches)))

                            (list (cadr(total-words-list speeches))
                                  (cadr(total-char/word-list speeches))))
                     ;#:title "Speech"
                     ;#:x-label "number of words in a speech "
                     ;#:y-label "average word length in the speech")
                     ))
             #:x-min 7
             #:x-max 20
             #:y-min 2
             #:y-max 10                 
             
             )]
     [else
         (plot (points (list (list (car(total-words-list speeches))
                              (car(total-char/word-list speeches)))
                                  
                        (list (cadr(total-words-list speeches))
                              (cadr(total-char/word-list speeches)))
                              
                        (list (caddr(total-words-list speeches))
                              (caddr(total-char/word-list speeches)))

                        (list(cadddr(total-words-list speeches))
                             (cadddr(total-char/word-list speeches))))
                  #:fill-color colors
                  #:sym 'fullcircle6
                  #:x-min 7
                  #:x-max 20
                  #:y-min 2
                  #:y-max 10))]

      )))
      


   
   

;;c;;


(define joe (/(car(total-char/word-list some-speeches))(car(total-words-list some-speeches))))
(define Jane (/ (cadr(total-char/word-list some-speeches))(cadr(total-words-list some-speeches))))
(define Jo (/(cadddr(total-char/word-list some-speeches)) (cadddr(total-words-list some-speeches))))
(define Jae (/ (caddr(total-char/word-list some-speeches))(caddr(total-words-list some-speeches))))


(define speech-histogram
  (lambda (speeches)
    (plot (discrete-histogram(list (list "Joe" joe)

                                   (list "Jane" Jane )

                                   (list "Jae" Jae)

                                   (list "Jo" Jo)
                                   )))))



; Examples/Tests:

;; +-----------+------------------------------------------------------
;; | Problem 6 |
;; +-----------+

; Time Log:
;   Date        Start   Finish  Elapsed Activity
;   3/02        2:00     2:55   Testing
; Time Spent: 

; Citations:

; Supplied code

; Solution:

;;; Procedure:
;;;   drop-any-lower-then-m
;;; Parameters:
;;;   a list of strings
;;; Purpose:
;;;   drop any string that is lower than M
;;; Produces:
;;;   a list of strings
;;; Preconditions:
;;;   A string of list that contains characters
;;; Postconditions:
;;;   First would compare the first aphlbate of the string and if it is lower then
;;;   then M then the the string will not be filter out. 


(define drop-any-lower-then-m
  (let* ([get-first-string (o car string->list)]
         [char-m #\M]
         [compare (section char-ci<=? <> char-m)]
         [char-m (o compare get-first-string)])
    (section filter (conjoin char-m) <>)))

;d. Explain how the code achieves its purpose.
#|
The code would first take out the first character of the string and compare it whether or
not it is lower then M. If it is the string will be filter our of the list. The function then
will take out all of the filter list and print it out
|#


; Examples/Tests:
#|
> (drop-less-then-3 '( "a" "b" "c"))
'("a" "b" "c")
> (drop-less-then-3 '( "a" "x" "c"))
'("a" "c")
> (drop-less-then-3 '( "abc" "xy" "cd"))
'("abc" "cd")
> (drop-less-then-3 '("A" "a" "B" "b" "C" "c" "D" "d" "E" "e" "F" "f" "G" "g" "H" "h" "I" "i" "J" "j" "K" "k" "L" "l" "M" "m" "N" "n" "O" "o" "P" "p" "Q" "q" "R" "r" "S" "s" "T" "t" "U"
        "u" "V" "v" "W" "w" "X" "x" "Y" "y" "Z" "z" ))
'("A" "a" "B" "b" "C" "c" "D" "d" "E" "e" "F" "f" "G" "g" "H" "h" "I" "i" "J" "j" "K" "k" "L" "l" "M" "m")
|#