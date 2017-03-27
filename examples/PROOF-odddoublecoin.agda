-- Agda program using the Iowa Agda library

open import bool

module PROOF-odddoublecoin
  (Choice : Set)
  (choose : Choice → 𝔹)
  (lchoice : Choice → Choice)
  (rchoice : Choice → Choice)
  where

open import eq
open import nat
open import list
open import maybe

---------------------------------------------------------------------------
-- Translated Curry operations:

add : ℕ → ℕ → ℕ
add zero x = x
add (suc y) z = suc (add y z)

-- Forward declaration:
odd : ℕ → 𝔹

even : ℕ → 𝔹
even zero = tt
even (suc x) = odd x

coin : Choice → ℕ → ℕ
coin c1 x = if choose c1 then x else suc x

double : ℕ → ℕ
double x = add x x

odd zero = ff
odd (suc x) = even x

---------------------------------------------------------------------------

add-suc : ∀ (x y : ℕ) → add x (suc y) ≡ suc (add x y)
add-suc zero y = refl
add-suc (suc x) y rewrite add-suc x y = refl

-- auxiliary property for x+x instead of double:
odd-add-x-x : ∀ (x : ℕ) → odd (add x x) ≡ ff
odd-add-x-x zero = refl
odd-add-x-x (suc x) rewrite add-suc x x | odd-add-x-x x = refl

odddoublecoin : (c1 : Choice) → (x : ℕ) → (odd (double (coin c1 x))) ≡ ff
odddoublecoin c1 x rewrite odd-add-x-x (coin c1 x) = refl

---------------------------------------------------------------------------
