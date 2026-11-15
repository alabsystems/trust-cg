; addhi0: for 0 <= P < 2^128 and 0 <= X < 2^64, the high 64 bits of (P + X*2^64) mod 2^128
; are ((P div 2^64) + X) mod 2^64
(set-logic ALL)
(define-fun P64 () Int 18446744073709551616)
(define-fun P128 () Int 340282366920938463463374607431768211456)
(define-fun r64 ((x Int)) Bool (and (<= 0 x) (< x P64)))
(declare-const p Int) (declare-const x Int)
(assert (and (<= 0 p) (< p P128) (r64 x)))
(assert (not (= (div (mod (+ p (* x P64)) P128) P64) (mod (+ (div p P64) x) P64))))
(check-sat)
