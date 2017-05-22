
import Reverse

---------------------------------------------------------------------
-- SUM

sum : List Nat -> Nat
sum [] = 0
sum (x :: xs) = x + sum xs

sum_tail' : List Nat -> Nat -> Nat
sum_tail' [] acc = acc
sum_tail' (x :: xs) acc = sum_tail' xs (x + acc)

sum_tail : List Nat -> Nat
sum_tail l = sum_tail' l 0

sum_tail_correct' : (xs : List Nat) -> (acc : Nat) -> sum_tail' xs acc = sum xs + acc
sum_tail_correct' [] acc = Refl
sum_tail_correct' (x :: xs) acc =
    rewrite sum_tail_correct' xs (x + acc) in
    rewrite plusCommutative x (sum xs) in
    rewrite plusAssociative (sum xs) x acc in
    Refl

sum_tail_correct : (l : List Nat) -> sum_tail l = sum l
sum_tail_correct xs =
    rewrite sum_tail_correct' xs 0 in
    rewrite plusZeroRightNeutral (sum xs) in 
    Refl

sum_cont' : {a : Type} -> List Nat -> (Nat -> a) -> a
sum_cont' [] k = k 0
sum_cont' (x :: xs) k = sum_cont' xs (\acc => k (x + acc))

sum_cont : List Nat -> Nat
sum_cont l = sum_cont' l id

sum_cont_correct' : (k : Nat -> a) -> (xs : List Nat) -> sum_cont' xs k = k (sum xs)
sum_cont_correct' k [] = Refl
sum_cont_correct' k (x :: xs) = sum_cont_correct' (\acc => k (plus x acc)) xs

sum_cont_correct : (l : List Nat) -> sum_cont l = sum l
sum_cont_correct = sum_cont_correct' id


---------------------------------------------------------------------
-- FIB

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


---------------------------------------------------------------------
-- MAP

map : (a -> b) -> List a -> List b
map f [] = []
map f (x :: xs) = f x :: map f xs

map_tail' : (a -> b) -> List a -> List b -> List b
map_tail' f [] acc = reverse2 acc
map_tail' f (x :: xs) acc = map_tail' f xs (f x :: acc)

map_tail : (a -> b) -> List a -> List b
map_tail f xs = map_tail' f xs []


map_tail_correct' : (f : a -> b) -> (xs : List a) -> (acc : List b) -> map_tail' f xs acc = reverse2 acc ++ map f xs
map_tail_correct' f [] acc = sym $ appendNilRightNeutral (reverse2 acc)
map_tail_correct' f (x :: xs) acc =
    rewrite map_tail_correct' f xs (f x :: acc) in
    rewrite proof_rev_app [f x] acc (map f xs) in
    rewrite proof_rev_app [] acc (f x :: map f xs) in
    Refl

map_tail_correct : (f : a -> b) -> (xs : List a) -> map_tail f xs = map f xs
map_tail_correct f xs = map_tail_correct' f xs []


---------------------------------------------------------------------
-- MACHINE

data Expr : Type where
    Const : Nat -> Expr
    Plus : Expr -> Expr -> Expr

eval_expr : Expr -> Nat
eval_expr (Const n) = n
eval_expr (Plus e1 e2) = eval_expr e1 + eval_expr e2

eval_expr_tail' : Expr -> Nat -> Nat
eval_expr_tail' (Const n) acc = n + acc
eval_expr_tail' (Plus e1 e2) acc = eval_expr_tail' e2 (eval_expr_tail' e1 acc)

eval_expr_tail : Expr -> Nat
eval_expr_tail e = eval_expr_tail' e 0

eval_expr_tail_correct' : (e : Expr) -> (acc : Nat) -> eval_expr_tail' e acc = eval_expr e + acc
eval_expr_tail_correct' (Const n) acc = Refl
eval_expr_tail_correct' (Plus e1 e2) acc =
    rewrite eval_expr_tail_correct' e1 acc in
    rewrite eval_expr_tail_correct' e2 (plus (eval_expr e1) acc) in
    rewrite plusAssociative (eval_expr e2) (eval_expr e1) acc in
    rewrite plusCommutative (eval_expr e2) (eval_expr e1) in
    Refl

eval_expr_tail_correct : (e : Expr) -> eval_expr_tail e = eval_expr e
eval_expr_tail_correct e =
    rewrite eval_expr_tail_correct' e 0 in
    rewrite plusZeroRightNeutral (eval_expr e) in
    Refl

eval_expr_cont' : Expr -> (Nat -> a) -> a
eval_expr_cont' (Const n) k = k n
eval_expr_cont' (Plus e1 e2) k = eval_expr_cont' e2 (\n2 =>
                               eval_expr_cont' e1 (\n1 => k (n1 + n2)))

eval_expr_cont : Expr -> Nat
eval_expr_cont e = eval_expr_cont' e id

eval_expr_cont_correct' : (e : Expr) -> (k : Nat -> a) -> eval_expr_cont' e k = k (eval_expr e)
eval_expr_cont_correct' (Const n) k = Refl
eval_expr_cont_correct' (Plus e1 e2) k =
    rewrite eval_expr_cont_correct' e2 (\n2 => eval_expr_cont' e1 (\n1 => k (plus n1 n2))) in
    rewrite eval_expr_cont_correct' e1 (\n1 => k (plus n1 (eval_expr e2))) in
    Refl

eval_expr_cont_correct : (e : Expr) -> eval_expr_cont e = eval_expr e
eval_expr_cont_correct e = rewrite eval_expr_cont_correct' e id in Refl


data Instr : Type where
    Push : Nat -> Instr
    Add : Instr

Prog : Type
Prog = List Instr

Stack : Type
Stack = List Nat

run : Prog -> Stack -> Stack
run [] s = s
run (Push n :: is) s = run is (n :: s)
run (Add :: is) (s1 :: s2 :: s) = run is (s1 + s2 :: s)
run (Add :: is) s = run is s

compile : Expr -> Prog
compile (Const n) = [Push n]
compile (Plus e1 e2) = compile e1 ++ compile e2 ++ [Add]

run_append : (xs : Prog) -> (ys : Prog) -> (s : Stack) -> run (xs ++ ys) s = run ys (run xs s)
run_append [] ys s = Refl
run_append (Push n :: xs) ys s = run_append xs ys (n :: s)
run_append (Add :: xs) ys (s1 :: s2 :: s) = run_append xs ys (plus s1 s2 :: s)
run_append (Add :: xs) ys [] = run_append xs ys []
run_append (Add :: xs) ys [s1] = run_append xs ys [s1]

compile_correct' : (e : Expr) -> (s : Stack) -> run (compile e) s = eval_expr e :: s
compile_correct' (Const n) s = Refl
compile_correct' (Plus e1 e2) s =
    rewrite run_append (compile e1) (compile e2 ++ [Add]) s in
    rewrite run_append (compile e2) [Add] (run (compile e1) s) in
    rewrite compile_correct' e1 s in
    rewrite compile_correct' e2 (eval_expr e1 :: s) in
    rewrite plusCommutative (eval_expr e2) (eval_expr e1) in
    Refl

compile_correct : (e : Expr) -> run (compile e) [] = [eval_expr e]
compile_correct e = compile_correct' e []
