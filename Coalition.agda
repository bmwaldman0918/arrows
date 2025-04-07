{-# OPTIONS --rewriting #-}
module Coalition where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat.Properties using (+-suc)
open import Data.Vec as Vec
open import Data.Vec.Properties using (∷-injectiveʳ)
open import Data.Bool using (Bool; not; true; false; _∧_; _≟_)
open import Data.Nat as ℕ hiding (_≟_)
open import Votes
open import Data.Fin as Fin hiding (_≟_)
open import Data.Product using (Σ; _×_; _,_; proj₂; proj₁; ∃)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Voter
open WeakPreference
open StrictPreference

Coalition : ℕ → Set
Coalition m = Vec Bool m

MembersCount : {m : ℕ} → Vec Bool m → ℕ
MembersCount c = count (λ x → x ≟ true) c

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
NonEmptyCoalition m = Σ (Coalition m) λ c → Σ (Fin m) λ i → (lookup c i) ≡ true

Unwrap : {m : ℕ} → NonEmptyCoalition m → Coalition m
Unwrap (fst , _) = fst

Intersect : {m : ℕ} → Coalition m → Coalition m → Coalition m
Intersect [] [] = [] 
Intersect (x ∷ xs) (y ∷ ys) = x ∧ y ∷ (Intersect xs ys)

SingletonCoalition : {m : ℕ} → Coalition m → Set
SingletonCoalition c = MembersCount c ≡ 1

FalseCoalition : (n : ℕ) → Coalition n
FalseCoalition zero    = []
FalseCoalition (suc n) = false ∷ FalseCoalition n

PrependFalseAgrees : {m n : ℕ} 
                   → {n>2 : n ℕ.> 2}
                   → (v : Votes n n>2 (m ℕ.+ 0))
                   → (a b : Fin n)
                   → CoalitionAgrees a b ((FalseCoalition m) ++ []) v
PrependFalseAgrees {zero} [] a b = empty-coalition-agrees
PrependFalseAgrees {suc m} (x ∷ v) a b = 
  false-agrees (FalseCoalition m ++ []) v (PrependFalseAgrees v a b) x


{-# REWRITE +-suc #-}
FalseCoalitionRearrange : {m m' : ℕ} 
  → (c : Coalition m')
  → FalseCoalition m ++ false ∷ c ≡ false ∷ FalseCoalition m ++ c 

FalseCoalitionRearrange {zero} c = refl
FalseCoalitionRearrange {suc m} c rewrite Eq.sym (FalseCoalitionRearrange {m} c) 
  = refl