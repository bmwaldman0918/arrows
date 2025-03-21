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
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit
open import Data.Bool as Bool

data Decisive-a>b {m n : ℕ} {n>2 : n ℕ.> 2} (c : Coalition m) (v : Votes n n>2 m) (a b : Fin n) : Set₁ where
  dec-a>b : (CoalitionAgrees a b c v) -- this should be a product
          → (CoalitionAgrees b a (InverseCoalition c) v) 
          → SWF v a b
          → Decisive-a>b c v a b 
{-
-- can we provide the arguments necessary to make this an inductive datatype?
-- maybe these should be defined wrt a similar coalition
data StrictlyDecisive-a>b {m n : ℕ} {n>2 : n ℕ.> 2} (c : Coalition m) (v : Votes n n>2 m) (a b : Fin n) : Set₁ where
  strictlydec-a>b : (CoalitionAgrees a b c v)
          → SWF v a b
          → StrictlyDecisive-a>b c v a b 
          -}
StrictlyDecisive-a>b : {m n : ℕ} → {n>2 : n ℕ.> 2}
             → Coalition m
             → Votes n n>2 m 
             → (a b : Fin n)
             → Set₁
--- what if all of this is defined wrt similar coalition
--- lemmas are actually producing this "similar coalition" instead of decisiveness
StrictlyDecisive-a>b c votes a b = (CoalitionAgrees a b c votes) → SWF votes a b

Decisive : {m n : ℕ} → {n>2 : n ℕ.> 2}
         → Coalition m
         → Votes n n>2 m
         → Set₁
Decisive c v = ∀ a b → StrictlyDecisive-a>b c v a b
