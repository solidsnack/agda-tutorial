
module exercize_2-1 where

open import Data.Nat
open import Data.Fin

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixl 100 _!_
_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[]       ! ()
(x ∷ xs) ! zero = x
(x ∷ xs) ! (suc i) = xs ! i 


Matrix : Set → ℕ → ℕ → Set
Matrix A n m = Vec (Vec A m) n   -- A type level function is no big deal.

vec : {n : ℕ}{A : Set} → A → Vec A n
vec {n} x with n
... | zero  = []
... | suc m = x ∷ vec {m} x

infixl 90 _$_
_$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
fs $ xs with fs | xs
... | f ∷ fs' | x ∷ xs' = f x ∷ fs' $ xs'
... | []      | []      = []

map : {n : ℕ}{A B : Set} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

upto : (n : ℕ) → Vec (Fin n) n
upto zero = []
upto (suc m) = zero ∷ map suc (upto m)

transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose {A} {n} {m} xss = map (λ m' → vecn m' $ xss) (upto m)
 where
  vecn : Fin m → Vec (Vec A m → A) n
  vecn m' = vec (λ xs → xs ! m')