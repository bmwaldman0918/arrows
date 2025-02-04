module Decisive where

open import Voter
open import Votes
open import Election
open import Coalition

open import Data.Fin as Fin using (_≟_; Fin)
open import Data.Nat as ℕ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty
open import Data.Product using (Σ; _×_; _,_)

Decisive-a>b : {m n : ℕ} → {n>1 : n ℕ.> 1}
             → {p1 p2 : ProtoCoalition m}
             → (split : Split-Coalitions p1 p2)
             → Votes n n>1 m 
             → (a b : Fin n)
             → Set₁
Decisive-a>b {p1 = p1} {p2 = p2} record { coalition-1 = coalition-1 
  ; coalition-2 = coalition-2 
  ; disj = disj 
  ; comp = comp } votes a b = (CoalitionAgrees votes a b p1) × (CoalitionAgrees votes b a p2) → SWF votes a b

StrictlyDecisive-a>b : {m n : ℕ} → {n>1 : n ℕ.> 1}
                     → {p1 p2 : ProtoCoalition m}
                     → (split : Split-Coalitions p1 p2)
                     → Votes n n>1 m 
                     → (a b : Fin n)
                     → Set₁
StrictlyDecisive-a>b {p1 = p1} record { coalition-1 = coalition-1 
  ; coalition-2 = coalition-2 
  ; disj = disj 
  ; comp = comp } votes a b = (CoalitionAgrees votes a b p1) → SWF votes a b

Decisive : {m n : ℕ} → {n>1 : n ℕ.> 1}
         → {p1 p2 : ProtoCoalition m}
         → (split : Split-Coalitions p1 p2)
         → Votes n n>1 m
         → Set₁
Decisive split v = ∀ a b → StrictlyDecisive-a>b split v a b
