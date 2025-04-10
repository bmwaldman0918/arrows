module Votes where
  
open import Voter
open WeakPreference using (Preference; R→Bool)
open StrictPreference using (P; P→Bool)
open PreferenceEquality
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕProp using (≤∧≢⇒<; <⇒≤; ≤-reflexive; n<1+n)
open import Data.Fin as Fin hiding (_+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Empty
open import Data.Bool
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Nullary.Decidable using (isYes)

data Votes (n : ℕ) (n>2 : n ℕ.> 2) : ℕ → Set₁ where
  []  : Votes n n>2 0
  _∷_ : {_R_ : Fin n → Fin n → Set} → {m : ℕ} → Preference n n>2 _R_ → Votes n n>2 m → Votes n n>2 (suc m)
open Votes

PredVotes : {n : ℕ} → {n>2 : n ℕ.> 2} → (m : ℕ) → Votes n n>2 (suc m) → Votes n n>2 m 
PredVotes m (x ∷ v) = v

HeadVotes : {n : ℕ} → {n>2 : n ℕ.> 2} → (m : ℕ) → Votes n n>2 (suc m) → Σ (Fin n → Fin n → Set) λ _R_ → Preference n n>2 _R_
HeadVotes m (_∷_ {_R_ = _R_} x v) = _R_ , x

Contains : {n m : ℕ} 
         → {n>2 : n ℕ.> 2} 
         → {_R_ : Fin n → Fin n → Set} 
         → Votes n n>2 m
         → Preference n n>2 _R_
         → Set
Contains {n} (p' ∷ votes) p = ≡-Preference p' p ⊎ Contains votes p
Contains [] R = ⊥

_⊆_ : {n m m' : ℕ} 
       → {n>2 : n ℕ.> 2} 
       → Votes n n>2 m
       → Votes n n>2 m'
       → Set
_⊆_ [] outer = ⊤
_⊆_ (p ∷ inner) outer = (Contains outer p) × (inner ⊆ outer)

Length : {n m : ℕ} → {n>2 : n ℕ.> 2} → Votes n n>2 m → ℕ
Length {m = m} _ = m

data Zip {n : ℕ} (n>2 : n ℕ.> 2) (a b : Fin n) : ℕ → Set₁ where
  z-nil : Zip n>2 a b 0
  z-cons : {r1 r2 : Fin n → Fin n → Set} 
         → {m : ℕ} 
         → (p1 : Preference n n>2 r1) 
         → (p2 : Preference n n>2 r2)
         → Zip n>2 a b m
         -----------
         → Zip n>2 a b (suc m)

Zipped : {m n : ℕ} → (n>2 : n ℕ.> 2) → (a b : Fin n) → (v1 v2 : Votes n n>2 m) → Zip n>2 a b m
Zipped n>2 a b [] [] = z-nil
Zipped n>2 a b (x ∷ v1) (y ∷ v2) = z-cons x y (Zipped n>2 a b v1 v2)

Similar : {n : ℕ} → {n>2 : n ℕ.> 2} → (m : ℕ) → (a b : Fin n) → Zip n>2 a b m → Set
Similar .0 a b z-nil = ⊤
Similar (suc m) a b (z-cons p1 p2 zip) = (P→Bool p1 a b ≡ P→Bool p2 a b) × (Similar m a b zip)

Get : {n : ℕ} → {n>2 : n ℕ.> 2} → (m idx : ℕ) → (m ℕ.> idx) → Votes n n>2 m → Σ (Fin n → Fin n → Set) λ _R_ → Preference n n>2 _R_
Get (suc m') zero (s≤s m>idx) votes = HeadVotes m' votes
Get (suc m') (suc idx) (s≤s m>idx) (x ∷ votes) = Get m' idx m>idx votes

ElectionAgrees : {m n : ℕ} → {n>2 : n ℕ.> 2} → (v : Votes n n>2 m) → (a b : Fin n) → Set
ElectionAgrees [] a b = ⊤ 
ElectionAgrees {m = suc m'} (x ∷ v) a b = P x a b × (ElectionAgrees v a b) 