
module Reverse
---------------------------------------------------------------------
-- REVERSE

reverse1 : List a -> List a
reverse1 [] = []
reverse1 (x :: xs) = reverse1 xs ++ [x]

proof_reverse1_one : (x : a) -> reverse1 [x] = [x]
proof_reverse1_one x = Refl

proof_reverse1_cons : (x : a) -> (xs : List a) -> reverse1 (x :: xs) = reverse1 xs ++ [x]
proof_reverse1_cons x xs = Refl

proof_reverse1_append : (xs : List a) -> (ys : List a) -> reverse1 (xs ++ ys) = reverse1 ys ++ reverse1 xs
proof_reverse1_append [] ys = rewrite appendNilRightNeutral (reverse1 ys) in Refl
proof_reverse1_append (x :: xs) ys =
    rewrite appendAssociative (reverse1 ys) (reverse1 xs) [x] in
    rewrite proof_reverse1_append xs ys in Refl

proof_reverse1_reverse1 : (xs : List a) -> xs = reverse1 (reverse1 xs)
proof_reverse1_reverse1 [] = Refl
proof_reverse1_reverse1 (x :: xs) =
    rewrite proof_reverse1_append (reverse1 xs) [x] in
    rewrite proof_reverse1_reverse1 xs in
    Refl


---------------------------------------------------------------------
-- COMPLEX REVERSE

public export
rev2 : List a -> List a -> List a
rev2 acc [] = acc
rev2 acc (x :: xs) = rev2 (x :: acc) xs

public export
reverse2 : List a -> List a
reverse2 xs = rev2 [] xs

proof_rev : (xs : List a) -> (ys : List a) -> rev2 xs ys = reverse2 ys ++ xs
proof_rev xs [] = Refl
proof_rev xs (y :: ys) =
    rewrite proof_rev [y] ys in
    rewrite sym $ appendAssociative (rev2 [] ys) [y] xs in
    rewrite proof_rev (y :: xs) ys in
    Refl

export
proof_rev_app : (xs : List a) -> (ys : List a) -> (zs : List a) -> rev2 xs ys ++ zs = rev2 (xs ++ zs) ys
proof_rev_app xs ys zs =
    rewrite proof_rev xs ys in
    rewrite proof_rev (xs ++ zs) ys in
    rewrite appendAssociative (rev2 [] ys) xs zs in
    Refl

proof_reverse1_reverse2 : (xs : List a) -> reverse1 xs = reverse2 xs
proof_reverse1_reverse2 [] = Refl
proof_reverse1_reverse2 (x :: xs) =
    rewrite proof_rev [x] xs in
    rewrite proof_reverse1_reverse2 xs in
    Refl

proof_reverse2_reverse2 : (xs : List a) -> xs = reverse2 (reverse2 xs)
proof_reverse2_reverse2 xs =
    rewrite sym $ proof_reverse1_reverse2 xs in
    rewrite sym $ proof_reverse1_reverse2 (reverse1 xs) in
    rewrite proof_reverse1_reverse1 xs in
    Refl
