-- Agda program using the Iowa Agda library

open import bool

module PROOF-permlength
  (Choice : Set)
  (choose : Choice → 𝔹)
  (lchoice : Choice → Choice)
  (rchoice : Choice → Choice)
  where

open import eq
open import bool
open import nat
open import list
open import maybe

---------------------------------------------------------------------------
-- Translated Curry operations:

insert : {a : Set} → Choice → a → 𝕃 a → 𝕃 a
insert c1 x [] = x :: []
insert c1 y (z :: u) = if choose c1 then y :: (z :: u) else z :: (insert (lchoice c1) y u)

perm : {a : Set} → Choice → 𝕃 a → 𝕃 a
perm c1 [] = []
perm c1 (x :: y) = insert c1 x (perm (lchoice c1) y)

---------------------------------------------------------------------------

insert-inc-length : ∀ {a : Set} → (ch : Choice) (x : a) (xs : 𝕃 a)
                 → length (insert ch x xs) ≡ suc (length xs)
insert-inc-length ch x [] = refl
insert-inc-length ch x (y :: ys) with choose ch
... | tt = refl
... | ff rewrite insert-inc-length (lchoice ch) x ys = refl


permlength : {a : Set} → (c1 : Choice) → (x : 𝕃 a) → (length x) ≡ (length (perm c1 x))
permlength c1 [] = refl
permlength c1 (x :: xs)
 rewrite insert-inc-length c1 x (perm (lchoice c1) xs)
         | permlength (lchoice c1) xs
  = refl

---------------------------------------------------------------------------
