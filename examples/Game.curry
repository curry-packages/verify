import Nat
import Test.Prop

data Move = L | R

len [] = Z
len (_:xs) = S (len xs)


main = solve  (S (S Z)) (S (S Z))

solve Z Z = []
solve (S x) y = L : solve x y
solve x (S y) = R : solve x y

-- Originally, we want to prove:
-- gamelength x y = len (solve x y) -=- add x y

-- If we are interested in the spine, i.e., the list structure of
-- calls to solve, we see that solve is strict in both arguments, i.e.,
-- (len (solve _|_ y)) and (len (solve x _|_)) have no values.
-- Thus, we can expand rules with variable arguments to rules with
-- all constructors:

solve1 Z     Z     = []
solve1 (S x) Z     = L : solve1 x     Z
solve1 (S x) (S y) = L : solve1 x     (S y)
solve1 Z     (S y) = R : solve1 Z     y
solve1 (S x) (S y) = R : solve1 (S x) y

-- Finally, we join the rules with identical left-hand sides:

solve2 Z     Z     = []
solve2 (S x) Z     = L : solve2 x Z
solve2 Z     (S y) = R : solve2 Z y
solve2 (S x) (S y) = L : solve2 x (S y) ? R : solve2 (S x) y

-- and prove:

gamelength x y = len (solve2 x y) -=- add x y
