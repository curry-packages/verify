-- Some basic structures and operation for dealing with non-deterministic values

module nondet where

open import bool
open import nat
open import list

infixr 8 _??_

----------------------------------------------------------------------
-- A tree datatype to represent non-deterministic value of some type.
-- It is either a value, a failure, or a choice between
-- non-deterministic values.
----------------------------------------------------------------------

data ND (A : Set) : Set where
  Val  : A → ND A
  _??_ : ND A → ND A → ND A

----------------------------------------------------------------------
-- Some operation to define functions working this the ND datatype:

-- Map a function on non-deterministic values:
mapND : {A B : Set} → (A → B) → ND A → ND B
mapND f (Val xs) = Val (f xs)
mapND f (t1 ?? t2) = mapND f t1 ?? mapND f t2

-- Extend the first argument to ND:
with-nd-arg : {A B : Set} → (A → ND B) → ND A → ND B
with-nd-arg f (Val x)    = f x
with-nd-arg f (t1 ?? t2) = with-nd-arg f t1 ?? with-nd-arg f t2

-- Extend the first argument of a binary function to ND:
with-nd-arg2 : {A B C : Set} → (A → B → ND C) → ND A → B → ND C
with-nd-arg2 f (Val x)    y = f x y
with-nd-arg2 f (t1 ?? t2) y = with-nd-arg2 f t1 y ?? with-nd-arg2 f t2 y

-- Extend the first argument of a ternary function to ND:
with-nd-arg3 : {A B C D : Set} → (A → B → C → ND D)
                               → ND A → B → C → ND D
with-nd-arg3 f (Val x)    y z = f x y z
with-nd-arg3 f (t1 ?? t2) y z = with-nd-arg3 f t1 y z ?? with-nd-arg3 f t2 y z

-- Apply a non-deterministic functional value to a non-determistic argument:
apply-nd : {A B : Set} → ND (A → B) → ND A → ND B
apply-nd (Val f) xs    = mapND f xs
apply-nd (t1 ?? t2) xs = apply-nd t1 xs ?? apply-nd t2 xs

-- Extend a deterministic function to one with non-deterministic result:
toND : {A B : Set} → (A → B) → A → ND B
toND f x = Val (f x)

-- Extend a deterministic function to a non-deterministic one:
det-to-nd : {A B : Set} → (A → B) → ND A → ND B
det-to-nd f = with-nd-arg (toND f)

----------------------------------------------------------------------
-- Some operations to define properties of non-deterministic values:

-- Count the number of values:
#vals : {A : Set} → ND A → ℕ
#vals (Val _) = 1
#vals (t1 ?? t2) = #vals t1 + #vals t2

-- Extract the list of all values:
vals-of : {A : Set} → ND A → 𝕃 A
vals-of (Val v)    = v :: []
vals-of (t1 ?? t2) = vals-of t1 ++ vals-of t2

-- All values in a Boolean tree are true:
always : ND 𝔹 → 𝔹
always (Val b)    = b
always (t1 ?? t2) = always t1 && always t2

-- There exists some true value in a Boolean tree:
eventually : ND 𝔹 → 𝔹
eventually (Val b)    = b
eventually (t1 ?? t2) = eventually t1 || eventually t2

-- There is not value:
failing : {A : Set} → ND A → 𝔹
failing (Val _)    = ff
failing (t1 ?? t2) = failing t1 && failing t2

-- All non-deterministic values satisfy a given predicate:
_satisfy_ : {A : Set} → ND A → (A → 𝔹) → 𝔹
(Val n)    satisfy p = p n
(t1 ?? t2) satisfy p = t1 satisfy p && t2 satisfy p

-- Every value in a tree is equal to the second argument w.r.t. a
-- comparison function provided as the first argument:
every : {A : Set} → (eq : A → A → 𝔹) → A → ND A → 𝔹
every eq x xs = xs satisfy (eq x)

----------------------------------------------------------------------
