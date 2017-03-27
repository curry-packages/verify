-- Definition of permutations and theorem about their length

import Test.Prop

insert x []     = [x]
insert x (y:ys) = (x : y : ys) ? (y : insert x ys)

perm []     = []
perm (x:xs) = insert x (perm xs)

permPreservesLength xs = length xs <~> length (perm xs)
