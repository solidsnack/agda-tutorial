module exercize_2-2 where

open import Function
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixl 100 _!_
_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[]       ! ()
(x ∷ xs) ! zero = x
(x ∷ xs) ! (suc i) = xs ! i 

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero}  f = []
tabulate {suc n} f = f zero ∷ tabulate (f ∘ suc)

lem-!-tab : ∀ {A n} (f : Fin n → A) (i : Fin n) → tabulate f ! i ≡ f i
lem-!-tab {_} {zero}  f ()
lem-!-tab {_} {suc m} f zero = refl
--lem-!-tab {_} {suc m} f zero with tabulate f | f zero
--... | x ∷ _ | y = refl
lem-!-tab {A} {suc m} f (suc h) with lem-!-tab {A} {suc m} f h
... | refl = {!refl!}
-- lem-!-tab {_} {suc m} f i = refl
--  where
--   tabulated = tabulate f
--   p : tabulated ! i ≡ f i
--   p = refl
  