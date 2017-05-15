-- Proof of very basic things contained in the base which are available as standard proofs (probably)

%hide id
%hide map

id : a -> a
id x = x

map : (a -> b) -> List a -> List b
map f [] = []
map f (x :: xs) = f x :: map f xs

proof_map_map : (xs : List a) -> map (f . g) xs = map f (map g xs)
proof_map_map [] = Refl
proof_map_map (x :: xs) = cong $ proof_map_map xs


---------------------------------------------------------------------
-- APPEND PROOFS

append : List a -> List a -> List a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

proof_append_nil : (xs : List a) -> append xs [] = xs
proof_append_nil [] = Refl
proof_append_nil (x :: xs) = cong $ proof_append_nil xs

proof_append_assoc : (xs : List a) -> (ys : List a) -> (zs : List a) -> append xs (append ys zs) = append (append xs ys) zs
proof_append_assoc [] ys zs = Refl
proof_append_assoc (x :: xs) ys zs = cong $ proof_append_assoc xs ys zs
