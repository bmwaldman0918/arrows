module Coalition where

open import Data.Vec as Vec
open import Data.Bool
open import Data.Nat as ℕ
open import Votes
open import Data.Fin as Fin
open import Data.Product using (Σ; _×_; _,_; proj₂; proj₁)
open import Voter
open WeakPreference
open StrictPreference

Coalition : ℕ → Set
Coalition m = Vec Bool m

FilteredVotes : {m n : ℕ} → {n>1 : n ℕ.> 1} → (c : Coalition m) → (v1 : Votes n n>1 m) → Σ ℕ λ m' → Votes n n>1 m'
FilteredVotes [] [] = 0 , [] 
FilteredVotes (false ∷ c) (x₁ ∷ v1) = FilteredVotes c v1 
FilteredVotes (true ∷ c) (head ∷ v1) with FilteredVotes c v1
... | m' , rem = (suc m') , (head ∷ rem)

InverseCoalition : {m : ℕ} → Coalition m → Coalition m
InverseCoalition [] = []
InverseCoalition (h ∷ c) = not h ∷ (InverseCoalition c)

data CoalitionAgrees {n : ℕ} {n>1 : n ℕ.> 1} (a b : Fin n) : {m : ℕ} → (c : Coalition m) → (v1 : Votes n n>1 m) → Set where
    empty-coalition-agrees : CoalitionAgrees a b [] []
    
    false-agrees : {m : ℕ} 
                 → (c : Coalition m) 
                 → (v : Votes n n>1 m)
                 → {_R_ : Fin n → Fin n → Set} 
                 → CoalitionAgrees a b c v 
                 → (p : Preference n n>1 _R_) 
                 → CoalitionAgrees a b (false Vec.∷ c) (p ∷ v)

    true-agrees : {m : ℕ} 
                → (c : Coalition m) → (v : Votes n n>1 m)
                → {_R_ : Fin n → Fin n → Set} 
                → CoalitionAgrees a b c v 
                → (p : Preference n n>1 _R_)
                → (P p a b)
                → CoalitionAgrees a b (true Vec.∷ c) (p ∷ v)

Whole : (m : ℕ) → (Coalition m)
Whole zero = [] 
Whole (suc m) = true ∷ (Whole m) 