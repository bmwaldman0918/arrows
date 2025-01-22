module Decisive where

open import Voter
open import Votes

open import Data.Fin as Fin using (_≟_; Fin)
open import Data.Nat as ℕ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty



{-
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
                → ¬ x ≡ y 
                → (election : Election n n>1 _R_ votes constitution)
                → Decisive n n>1 votes coalition constitution x y election
                → ∀ a b → Decisive n n>1 votes coalition constitution a b election
FieldExpansion n n>1 votes coalition _ x y ¬x≡y election decisive a b
  with a Fin.≟ x | a Fin.≟ y | b Fin.≟ x | b Fin.≟ y
... | yes a≡x | yes a≡y | _ | _ = ⊥-elim (¬x≡y (Eq.trans (Eq.sym a≡x) a≡y))
... | _ | _ | yes b≡x | yes b≡y = ⊥-elim (¬x≡y (Eq.trans (Eq.sym b≡x) b≡y))
... | yes a≡x | _ | _ | yes b≡y rewrite b≡y | a≡x = decisive
... | a≟x | a≟y | b≟x | b≟y = {!   !}
-}