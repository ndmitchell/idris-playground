-- Reported upstream as https://github.com/idris-lang/Idris-dev/issues/3809

fibb : Nat -> Nat
fibb Z = 0
fibb (S Z) = 1
fibb (S (S n)) = fibb (S n) + fibb n

fib_tail' : Nat -> Nat -> Nat -> Nat
fib_tail' n a b = case n of
    Z => b
    S n' => fib_tail' n' (a + b) a -- WORKS
    -- S n => fib_tail' n (a + b) a -- BREAKS

fib_tail : Nat -> Nat
fib_tail n = fib_tail' n 1 0

fib_tail_correct' : (d : Nat) -> (u : Nat) -> fib_tail' d (fibb (S u)) (fibb u) = fibb (d+u)
fib_tail_correct' Z u = Refl
fib_tail_correct' (S d) u = ?todo
