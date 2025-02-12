module Election where

open import Voter
open WeakPreference using (Preference)
open import Votes

open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Vec as Vec
open import Data.Bool as Bool
open import Data.Product using (Σ)

private
    variable
        n : ℕ
        n>1 : n ℕ.> 1
        a b c : Fin n
        _R_ : Fin n → Fin n → Set

data SWF {m n : ℕ} {n>1 : n ℕ.> 1} (v : Votes n n>1 m) : Fin n → Fin n → Set₁ where
  Transitivity : (a b c : Fin n) 
               → SWF v a b 
               → SWF v b c 
               → SWF v a c
  BinaryIIA : (a b : Fin n)
            → (v1 : Votes n n>1 m)
            → Similar m a b (Zipped n>1 a b v v1)
            → SWF v1 a b
            → SWF v a b
  Pareto : (a b : Fin n)
         → ElectionAgrees v a b
         → SWF v a b 
