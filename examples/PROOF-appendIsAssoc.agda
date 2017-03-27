-- Agda program using the Iowa Agda library

open import bool

module PROOF-appendIsAssoc
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

data List (a : Set) : Set where
   Empty : List a
   Cons : a → List a → List a

append : {a : Set} → List a → List a → List a
append Empty x = x
append (Cons y z) u = Cons y (append z u)

---------------------------------------------------------------------------

appendIsAssoc : {a : Set} → (x : List a) → (y : List a) → (z : List a)
              → (append (append x y) z) ≡ (append x (append y z))
appendIsAssoc Empty y z = refl
appendIsAssoc (Cons x xs) y z rewrite appendIsAssoc xs y z = refl

---------------------------------------------------------------------------
