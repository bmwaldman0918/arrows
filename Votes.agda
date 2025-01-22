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

{- each entry in a zip is a record with 3 parts: 
  2 candidates, 
  2 voters and 
  a proof that the r->bool for the two voters as defined over both candidates is equal 
-}
-- a coalition is a dependent type but its a list of strictly numbers less than m

{-
Coalition : (n m : ℕ) → (n>1 : n ℕ.> 1) → (Votes n n>1 m) → Set₁
Coalition n n>1 votes = Σ (Votes n n>1) (λ coalition → coalition ⊆ votes)

Coalition-x>y : (n : ℕ) 
              → (n>1 : n ℕ.> 1) 
              → (votes : Votes n n>1)
              → Coalition n n>1 votes
              → (x y : Fin n)
              → Set
Coalition-x>y n n>1 votes ([] , _) x y = ⊤ 
Coalition-x>y n n>1 votes ((v ∷ rem) , v∈votes , rem⊆votes) x y 
            = P→Bool v x y ≡ true × (Coalition-x>y n n>1 votes (rem , rem⊆votes) x y) 
            -}