{-# OPTIONS --rewriting #-}
module Decisive where

open import Voter
open import Votes
open import Election
open import Coalition
open WeakPreference
open StrictPreference

open import Data.Fin as Fin using (_≟_; Fin)
open import Data.Nat as ℕ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit
open import Data.Bool as Bool

private
    variable
        m n : ℕ
        n>2 : n ℕ.> 2

Decisive-a>b : (c : Coalition m) 
               (v : Votes n n>2 m) 
               (Result : Votes n n>2 m → Fin n → Fin n → Set) 
               (a b : Fin n)
               → Set₁ 
Decisive-a>b c v result a b = 
  (CoalitionAgrees a b c v) × (CoalitionAgrees b a (InverseCoalition c) v) × result v a b
{-
-- can we provide the arguments necessary to make this an inductive datatype?
-- maybe these should be defined wrt a similar coalition
data StrictlyDecisive-a>b {m n : ℕ} {n>2 : n ℕ.> 2} (c : Coalition m) (v : Votes n n>2 m) (a b : Fin n) : Set₁ where
  strictlydec-a>b : (CoalitionAgrees a b c v)
          → SWF v a b
          → StrictlyDecisive-a>b c v a b 
          -}
StrictlyDecisive-a>b : Coalition m
             → Votes n n>2 m
             → (Votes n n>2 m → Fin n → Fin n → Set) 
             → (a b : Fin n)
             → Set₁
--- what if all of this is defined wrt similar coalition
--- lemmas are actually producing this "similar coalition" instead of decisiveness
StrictlyDecisive-a>b c votes result a b = (CoalitionAgrees a b c votes) → result votes a b

Decisive : Coalition m
         → Votes n n>2 m
         → (Votes n n>2 m → Fin n → Fin n → Set)
         → Set₁
Decisive c v result = ∀ a b → StrictlyDecisive-a>b c v result a b

Dictator : (v : Votes n n>2 m) 
         → (Result : Votes n n>2 m → Fin n → Fin n → Set)
         → Set₁
Dictator {m = m} ballots Result = Σ (SingletonCoalition m) λ c → Decisive (c .proj₁) ballots Result   