
module BugXXXImp

rev2 : List a -> List a -> List a
rev2 acc [] = acc
rev2 acc (x :: xs) = rev2 (x :: acc) xs

export
rev : List a -> List a
rev = rev2 []

export
revNil : rev [] = []
revNil = Refl
