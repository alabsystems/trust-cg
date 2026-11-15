; (u + k*2^128) mod 2^128 = u mod 2^128, any integers u, k
(set-logic ALL)
(define-fun P64 () Int 18446744073709551616)
(define-fun P128 () Int 340282366920938463463374607431768211456)
(define-fun r64 ((x Int)) Bool (and (<= 0 x) (< x P64)))
(declare-const u Int) (declare-const k Int)
(assert (not (= (mod (+ u (* k P128)) P128) (mod u P128))))
(check-sat)
