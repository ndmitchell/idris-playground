
fibExp : Nat -> Nat
fibExp Z = 0
fibExp (S Z) = 1
fibExp (S (S n)) = fibExp (S n) + fibExp n

fibLin' : Nat -> Nat -> Nat -> Nat
fibLin' Z a b = b
fibLin' (S n) a b = fibLin' n (a + b) a

fibLin : Nat -> Nat
fibLin n = fibLin' n 1 0

fibLinInvariant : (d : Nat) -> (u : Nat) -> fibLin' d (fibExp (1+u)) (fibExp u) = fibExp (d+u)
fibLinInvariant Z u = Refl
fibLinInvariant (S d) u =
    rewrite fibLinInvariant d (S u) in
    rewrite plusSuccRightSucc d u in
    Refl

fibEq : (n : Nat) -> fibLin n = fibExp n
fibEq n =
    rewrite fibLinInvariant n 0 in
    rewrite plusZeroRightNeutral n in
    Refl
