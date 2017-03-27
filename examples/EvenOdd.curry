-- Mutual recursive definition of even:

import Nat
import Test.Prop

double x = add x x

coin x = x ? S x

even :: Nat -> Bool
even Z = True
even (S n) = odd n

odd :: Nat -> Bool
odd Z = False
odd (S n) = even n

odddoublecoin x = odd (double (coin x)) <~> False


