module Votes where
  
open import Voter
open WeakPreference using (Preference; R→Bool)
open StrictPreference using (P; P→Bool)
open PreferenceEquality
open import Data.Nat as ℕ
open import Data.Fin as Fin hiding (_+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Empty
open import Data.Bool
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)

data Votes (n : ℕ) (n>1 : n ℕ.> 1) : ℕ → Set₁ where
  []  : Votes n n>1 0
  _∷_ : {_R_ : Fin n → Fin n → Set} → {m : ℕ} → Preference n n>1 _R_ → Votes n n>1 m → Votes n n>1 (suc m)

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

-- for BinaryIIA, lets zip the two votes together and get proofs that r→bool is equal for the whole zip
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

Agrees : (m n : ℕ) → (n>1 : n ℕ.> 1) → (a b : Fin n) → Votes n n>1 m → Set
Agrees .0 n n>1 a b [] = ⊤
Agrees (suc m) n n>1 a b (x ∷ v) = P x a b × Agrees m n n>1 a b v

data Coalition (m : ℕ) : Set where
  c-single : (idx : ℕ) → (m ℕ.≥ idx) → Coalition m
  c-cons : (idx : ℕ) → (m ℕ.≥ idx) → Coalition m → Coalition m

Get-helper : (m n idx : ℕ) → (n>1 : n ℕ.> 1) → (m ℕ.> idx) → Votes n n>1 m → (Fin n → Fin n → Set)
Get-helper (suc m') n idx n>1 m>idx (x ∷ v) with m' ℕ.≟ idx 
Get-helper (suc m') n idx n>1 m>idx (_∷_ {_R_} x v) | true because _ = _R_ 
... | false because ofⁿ ¬p = Get-helper m' n idx n>1 {!   !} v 

-- Get -- first gets the type of the function from gethelper and returns a proof that it is a preference
-- from get, we construct a list of voters that we can then perform operations on
-- questions for stu:
  -- thoughts on constructors as functions
  -- thoughts on the use of bot/top types