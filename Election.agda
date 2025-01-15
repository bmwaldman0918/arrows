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

module Constitution where
  Constitution : (n : ℕ) 
               → (n>1 : n ℕ.> 1) 
               → (_R_ : Fin n → Fin n → Set) 
               ----------
               → Set
  Constitution = Preference

  Election : (n : ℕ) 
           → (n>1 : n ℕ.> 1)
           → (_R_ : Fin n → Fin n → Set)
           → Votes n n>1
           → Constitution n n>1 _R_
           ------------------------
           → Set
  Election n n>1 _R_ vec cons = Constitution n n>1 _R_
open Constitution