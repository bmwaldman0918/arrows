module Decisive where

open import Voter
open import Votes
open import Election

open import Data.Fin as Fin using (_≟_; Fin)
open import Data.Nat as ℕ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty
open import Data.Product using (Σ; _×_; _,_)

Decisive-a>b : (m n : ℕ) → (n>1 : n ℕ.> 1) 
         → (c : Coalition m)
         → (ac : Anti-coalition m c)
         → Votes n n>1 m 
         → (a b : Fin n)
         → Set₁
Decisive-a>b m n n>1 c (ac , _) v a b = 
  Coalition-Agrees m n n>1 c v a b × Coalition-Agrees m n n>1 ac v b a
  → SWF m n n>1 v a b

StrictlyDecisive-a>b : (m n : ℕ) → (n>1 : n ℕ.> 1) 
         → (c : Coalition m)
         → Votes n n>1 m 
         → (a b : Fin n)
         → Set₁
StrictlyDecisive-a>b m n n>1 c v a b = 
  Coalition-Agrees m n n>1 c v a b
  → SWF m n n>1 v a b

Decisive : (m n : ℕ) → (n>1 : n ℕ.> 1) 
         → (c : Coalition m)
         → (v : Votes n n>1 m)
         → Set₁
Decisive m n n>1 c v = ∀ a b → StrictlyDecisive-a>b m n n>1 c v a b