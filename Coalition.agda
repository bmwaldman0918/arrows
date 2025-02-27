module Coalition where

open import Data.Vec as Vec
open import Data.Bool
open import Data.Nat as ℕ
open import Votes
open import Data.Fin as Fin
open import Data.Product using (Σ; _×_; _,_; proj₂; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Voter
open WeakPreference
open StrictPreference

Coalition : ℕ → Set
Coalition m = Vec Bool m

FilteredVotes : {m n : ℕ} → {n>2 : n ℕ.> 2} → (c : Coalition m) → (v2 : Votes n n>2 m) → Σ ℕ λ m' → Votes n n>2 m'
FilteredVotes [] [] = 0 , [] 
FilteredVotes (false ∷ c) (x₁ ∷ v2) = FilteredVotes c v2 
FilteredVotes (true ∷ c) (head ∷ v2) with FilteredVotes c v2
... | m' , rem = (suc m') , (head ∷ rem)

InverseCoalition : {m : ℕ} → Coalition m → Coalition m
InverseCoalition [] = []
InverseCoalition (h ∷ c) = not h ∷ (InverseCoalition c)

data CoalitionAgrees {n : ℕ} {n>2 : n ℕ.> 2} (a b : Fin n) : {m : ℕ} → (c : Coalition m) → (v2 : Votes n n>2 m) → Set₁ where
    empty-coalition-agrees : CoalitionAgrees a b [] []
    
    false-agrees : {m : ℕ} 
                 → (c : Coalition m) 
                 → (v : Votes n n>2 m)
                 → {_R_ : Fin n → Fin n → Set} 
                 → CoalitionAgrees a b c v 
                 → (p : Preference n n>2 _R_) 
                 → CoalitionAgrees a b (false Vec.∷ c) (p ∷ v)

    true-agrees : {m : ℕ} 
                → (c : Coalition m) → (v : Votes n n>2 m)
                → {_R_ : Fin n → Fin n → Set} 
                → CoalitionAgrees a b c v 
                → (p : Preference n n>2 _R_)
                → (P p a b)
                → CoalitionAgrees a b (true Vec.∷ c) (p ∷ v)

Whole : (m : ℕ) → (Coalition m)
Whole zero = [] 
Whole (suc m) = true ∷ (Whole m) 

NonEmptyCoalition : (m : ℕ) → Set
NonEmptyCoalition m = Σ (Coalition m) λ c → Σ (Fin m) λ i → lookup c i ≡ true

Unwrap : {m : ℕ} → NonEmptyCoalition m → Coalition m
Unwrap (fst , _) = fst