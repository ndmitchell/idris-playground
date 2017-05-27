
fibExp 0 = 0
fibExp 1 = 1
fibExp n = fibExp (n-1) + fibExp (n-2)

fibLin' 0 a b = a
fibLin' n a b = fibLin' (n-1) b (a+b)

fibLin n = fibLin' n 0 1

fibLog' 0 = (0, 1)
fibLog' 1 = (1, 1)
fibLog' n
 | odd n     = (a*a + b*b, c*c - a*a)
 | otherwise = (c*c - a*a, b*b + c*c)
 where (a,b) = fibLog' ((n-1) `div` 2)
       c     = a + b

fibLog = fst . fibLog'
