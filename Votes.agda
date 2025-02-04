module Votes where
  
open import Voter
open WeakPreference using (Preference; R→Bool)
open StrictPreference using (P; P→Bool)
open PreferenceEquality
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕProp using (≤∧≢⇒<; <⇒≤; ≤-reflexive)
open import Data.Fin as Fin hiding (_+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Empty
open import Data.Bool
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Nullary.Decidable using (isYes)

data Votes (n : ℕ) (n>1 : n ℕ.> 1) : ℕ → Set₁ where
  []  : Votes n n>1 0
  _∷_ : {_R_ : Fin n → Fin n → Set} → {m : ℕ} → Preference n n>1 _R_ → Votes n n>1 m → Votes n n>1 (suc m)
open Votes

record VoterProd (n : ℕ) (n>1 : n ℕ.> 1) : Set₁ where
  field
    VPR : (Fin n → Fin n → Set)
    VPP : Preference n n>1 VPR
open VoterProd

Contains : {n m : ℕ} 
         → {n>1 : n ℕ.> 1} 
         → {_R_ : Fin n → Fin n → Set} 
         → Votes n n>1 m
         → Preference n n>1 _R_
         → Set
Contains {n} (p' ∷ votes) p = ≡-Preference p' p ⊎ Contains votes p
Contains [] R = ⊥

_⊆_ : {n m m' : ℕ} 
       → {n>1 : n ℕ.> 1} 
       → Votes n n>1 m
       → Votes n n>1 m'
       → Set
_⊆_ [] outer = ⊤
_⊆_ (p ∷ inner) outer = (Contains outer p) × (inner ⊆ outer)

Length : {n m : ℕ} → {n>1 : n ℕ.> 1} → Votes n n>1 m → ℕ
Length {m = m} _ = m

data Zip (n : ℕ) (n>1 : n ℕ.> 1) (a b : Fin n) : ℕ → Set₁ where
  z-nil : Zip n n>1 a b 0
  z-cons : {r1 r2 : Fin n → Fin n → Set} 
         → {m : ℕ} 
         → (p1 : Preference n n>1 r1) 
         → (p2 : Preference n n>1 r2)
         → Zip n n>1 a b m
         -----------
         → Zip n n>1 a b (suc m)
Zipped : (m n : ℕ) → (n>1 : n ℕ.> 1) → (a b : Fin n) → (v1 v2 : Votes n n>1 m) → Zip n n>1 a b m
Zipped zero n n>1 a b [] [] = z-nil
Zipped (suc m) n n>1 a b (x ∷ v1) (y ∷ v2) = z-cons x y (Zipped m n n>1 a b v1 v2)

Similar : (m n : ℕ) → (n>1 : n ℕ.> 1) → (a b : Fin n) → Zip n n>1 a b m → Set
Similar .0 n n>1 a b z-nil = ⊤
Similar (suc m) n n>1 a b (z-cons p1 p2 zip) = (R→Bool p1 a b ≡ R→Bool p2 a b) × (Similar m n n>1 a b zip)

data ElectionAgrees (n : ℕ) (n>1 : n ℕ.> 1) (a b : Fin n) : {m : ℕ} → Votes n n>1 m → Set₁ where
  empty-election-agrees : ElectionAgrees n n>1 a b []

  cons-election-agrees  : {_R_ : Fin n → Fin n → Set}
                        → {m : ℕ}
                        → (v : Preference n n>1 _R_)
                        → (P v a b)
                        → (rem : Votes n n>1 m)
                        → ElectionAgrees n n>1 a b rem
                        ------------------------------------
                        → ElectionAgrees n n>1 a b (v ∷ rem)

Get-helper : (m n idx : ℕ) → (n>1 : n ℕ.> 1) → (m ℕ.> idx) → Votes n n>1 m → VoterProd n n>1
Get-helper (suc m') n idx n>1 m>idx (x ∷ v) with m' ℕ.≟ idx 
Get-helper (suc m') n idx n>1 m>idx (_∷_ {_R_} x v) | true because _ = record { VPR = _R_ ; VPP = x }
Get-helper (suc m') n idx n>1 (s≤s m>idx) (x ∷ v) | false because ofⁿ ¬p = Get-helper m' n idx n>1 (ℕProp.≤∧≢⇒< m>idx λ idx≡m' → ¬p (Eq.sym idx≡m')) v 

Get : (m n idx : ℕ) → (n>1 : n ℕ.> 1) → (m>idx : m ℕ.> idx) → (v : Votes n n>1 m) → Preference n n>1 (VPR (Get-helper m n idx n>1 m>idx v))
Get (suc m') n idx n>1 m>idx v with Get-helper (suc m') n idx n>1 m>idx v
... | record { VPR = VPR₁ ; VPP = VPP₁ } = VPP₁
