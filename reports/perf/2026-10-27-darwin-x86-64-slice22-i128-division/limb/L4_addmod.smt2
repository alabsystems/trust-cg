; ((p mod 2^64) + (q mod 2^64)) mod 2^64 = (p + q) mod 2^64: bvadd of two 64-bit bvmul is the sum's low 64 bits
(set-logic ALL)
(define-fun P64 () Int 18446744073709551616)
(define-fun P128 () Int 340282366920938463463374607431768211456)
(define-fun r64 ((x Int)) Bool (and (<= 0 x) (< x P64)))
(declare-const p Int) (declare-const q Int)
(assert (not (= (mod (+ (mod p P64) (mod q P64)) P64) (mod (+ p q) P64))))
(check-sat)
