%default partial

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

isEven : Nat -> Bool
isEven Z = True
isEven (S Z) = False
isEven (S (S x)) = isEven x

sub : Nat -> Nat -> Nat
sub (S x) (S y) = sub x y
sub x _ = x

fibLog' : Nat -> (Nat, Nat)
fibLog' Z = (0, 1)
fibLog' (S Z) = (1, 1)
fibLog' (S (S n)) with (fibLog' (S n `div` 2), isEven n)
    fibLog' (S (S n)) ((a, b), True) = (c*c `sub` a*a, b*b + c*c)
    fibLog' (S (S n)) ((a, b), True)

 =
    if isEven n then (c*c `sub` a*a, b*b + c*c)
                else (a*a + b*b, c*c `sub` a*a)
 where
     ab : (Nat, Nat)
     ab = fibLog' (S n `div` 2)
     a = fst ab
     b = snd ab
     c = a + b

fibLog : Nat -> Nat
fibLog = fst . fibLog'

fibLogInvariant : (x : Nat) -> fibLog' x = (fibExp x, fibExp (1+x))
fibLogInvariant Z = ?todo_z
fibLogInvariant (S Z) = ?todo_sz
fibLogInvariant (S (S x)) = ?todo

