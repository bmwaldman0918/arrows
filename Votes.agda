module Votes where
  
open import Voter
open WeakPreference using (Preference; R→Bool)
open StrictPreference using (P; P→Bool)
open PreferenceEquality
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕProp using (≤∧≢⇒<)
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

data ProtoCoalition (m : ℕ) : Set where
  empty : ProtoCoalition m
  c-cons : (idx : ℕ) → (m ℕ.> idx) → ProtoCoalition m → ProtoCoalition m
-- i think ill want to package a contains proof in get-helper too
-- maybe should be increasing and duplication free

In-Coalition : (m i : ℕ) → (m ℕ.> i) → ProtoCoalition m → Set
In-Coalition m i _ empty = ⊥
In-Coalition m i m>i (c-cons idx x coal) = i ≡ idx ⊎ In-Coalition m i m>i coal

Increasing : (m : ℕ) → ProtoCoalition m → Set
Increasing m empty = ⊤
Increasing m (c-cons idx x empty) = ⊤
Increasing m (c-cons i _ (c-cons i' m>i' pc)) = i ℕ.< i' × Increasing m (c-cons i' m>i' pc)

UniqueEntries : (m : ℕ) → ProtoCoalition m → Set
UniqueEntries m empty = ⊤
UniqueEntries m (c-cons idx m>idx pc) = ¬ In-Coalition m idx m>idx pc × UniqueEntries m pc

record Coalition (m : ℕ) (p : ProtoCoalition m) : Set where
  field
    inc : Increasing m p
    uq-entries : UniqueEntries m p

Get-helper : (m n idx : ℕ) → (n>1 : n ℕ.> 1) → (m ℕ.> idx) → Votes n n>1 m → VoterProd n n>1
Get-helper (suc m') n idx n>1 m>idx (x ∷ v) with m' ℕ.≟ idx 
Get-helper (suc m') n idx n>1 m>idx (_∷_ {_R_} x v) | true because _ = record { VPR = _R_ ; VPP = x }
Get-helper (suc m') n idx n>1 (s≤s m>idx) (x ∷ v) | false because ofⁿ ¬p = Get-helper m' n idx n>1 (ℕProp.≤∧≢⇒< m>idx λ idx≡m' → ¬p (Eq.sym idx≡m')) v 

Get : (m n idx : ℕ) → (n>1 : n ℕ.> 1) → (m>idx : m ℕ.> idx) → (v : Votes n n>1 m) → Preference n n>1 (VPR (Get-helper m n idx n>1 m>idx v))
Get (suc m') n idx n>1 m>idx v with Get-helper (suc m') n idx n>1 m>idx v
... | record { VPR = VPR₁ ; VPP = VPP₁ } = VPP₁

Coalition-Agrees : (m n : ℕ) → (n>1 : n ℕ.> 1) → ProtoCoalition m → Votes n n>1 m → (a b : Fin n) → Set
Coalition-Agrees m n n>1 empty _ _ _ = ⊤
Coalition-Agrees m n n>1 (c-cons idx m>idx coalition) votes a b = (P (Get m n idx n>1 m>idx votes) a b) × (Coalition-Agrees m n n>1 coalition votes a b)

Disjoint∧Complete : (m : ℕ) → (c1 c2 : ProtoCoalition m) → Set
Disjoint∧Complete m c1 c2 = ∀ n → (m>n : m ℕ.> n) → ((In-Coalition m n m>n c1) × ¬ (In-Coalition m n m>n c2)) 
                                         ⊎ ((In-Coalition m n m>n c2) × ¬ (In-Coalition m n m>n c1))

Anti-coalition : (m : ℕ) → (c : ProtoCoalition m) → Set
Anti-coalition m c = Σ (ProtoCoalition m) (λ c' → Disjoint∧Complete m c c')
