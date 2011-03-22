
module exercize_2-1 where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open DecTotalOrder Data.Nat.decTotalOrder using (trans; refl)
open import Data.Fin using (Fin; suc; zero; fromℕ≤)

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

n≤n+1 : {m : ℕ} → m ≤ suc m
n≤n+1 = ≤-step refl

upto : (n : ℕ) → Vec (Fin n) n
upto n = upto' n refl
 where
  upto' : (m : ℕ) → (m ≤ n) → Vec (Fin n) m
  upto' zero m≤n  = []
  upto' (suc m') m≤n = fromℕ≤ m≤n ∷ upto' m' (trans n≤n+1 m≤n)


transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose {A} {n} {m} xss = map (λ m' → vecn m' $ xss) (upto m)
 where
  vecn : Fin m → Vec (Vec A m → A) n
  vecn m' = vec (λ xs → xs ! m')