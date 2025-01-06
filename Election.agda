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

module Election where
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
open Election

module Decisive where
  Decisive : (n : ℕ) 
           → (n>1 : n ℕ.> 1)
           → (votes : Votes n n>1)
           → (coalition : Coalition n n>1 votes)
           → {_R_ : Fin n → Fin n → Set}
           → (constitution : Constitution n n>1 _R_)
           → (x y : Fin n)
           → Election n n>1 _R_ votes constitution
           → Set
  Decisive n n>1 votes coalition {_R_ = _R_} _ x y election = Coalition-x>y n n>1 votes coalition x y → x R y
  
  FieldExpansion : (n : ℕ) 
                 → (n>1 : n ℕ.> 1)
                 → (votes : Votes n n>1)
                 → (coalition : Coalition n n>1 votes)
                 → (_R_ : Fin n → Fin n → Set)
                 → {constitution : Constitution n n>1 _R_}
                 → (x y : Fin n)
                 → (election : Election n n>1 _R_ votes constitution)
                 → Decisive n n>1 votes coalition constitution x y election
                 → ∀ a b → Decisive n n>1 votes coalition constitution a b election
  FieldExpansion n n>1 votes coalition _ x y election decisive a b = λ {c-x>y → {!   !}} 