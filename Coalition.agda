module Coalition where

open import Votes using (Votes; VoterProd; Get)
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

data ProtoCoalition (m : ℕ) : Set where
  empty : ProtoCoalition m
  c-cons : (idx : ℕ) → (m ℕ.> idx) → ProtoCoalition m → ProtoCoalition m

Lift : {m : ℕ} → ProtoCoalition m → ProtoCoalition (suc m)
Lift empty = empty
Lift (c-cons idx x p) = c-cons idx (s≤s (ℕProp.<⇒≤ x)) (Lift p)

data InCoalition (m : ℕ) : ℕ → ProtoCoalition m → Set where
  in-coalition-head : (i : ℕ) 
                    → (m>i : m ℕ.> i) 
                    → (pc : ProtoCoalition m)
                    -----------------------------------
                    → InCoalition m i (c-cons i m>i pc)

  in-coalition-tail : (i i' : ℕ) 
                    → (m>i : m ℕ.> i) 
                    → (pc : ProtoCoalition m)
                    → InCoalition m i' pc
                    ------------------------------------
                    → InCoalition m i' (c-cons i m>i pc)

data Increasing (m : ℕ) : ProtoCoalition m → Set where
  empty-inc     : Increasing m empty
  
  singleton-inc : (i : ℕ) 
                → (m>i : m ℕ.> i)
                -----------------------------------
                → Increasing m (c-cons i m>i empty)

  cons-inc      : (i i' : ℕ) 
                → (m>i' : m ℕ.> i')
                → (m>i : m ℕ.> i) 
                → (i' ℕ.> i) 
                → (pc : ProtoCoalition m) 
                → Increasing m (c-cons i' m>i' pc)
                -------------------------------------------------
                → Increasing m (c-cons i m>i (c-cons i' m>i' pc))

data UniqueEntries (m : ℕ) : ProtoCoalition m → Set where
  empty-uq-entries : UniqueEntries m empty

  cons-uq-entries  : (i : ℕ)
                   → (m>i : m ℕ.> i)
                   → (pc : ProtoCoalition m)
                   → ¬ InCoalition m i pc
                   → UniqueEntries m pc
                   -----------------------------------
                   → UniqueEntries m (c-cons i m>i pc)

record Coalition (m : ℕ) (p : ProtoCoalition m) : Set where
  field
    inc : Increasing m p
    uq-entries : UniqueEntries m p

EmptyCoalition : (m : ℕ) → Coalition m empty
EmptyCoalition m = record { inc = empty-inc ; uq-entries = empty-uq-entries } 

data CoalitionAgrees {m n : ℕ} {n>1 : n ℕ.> 1} (votes : Votes n n>1 m) (a b : Fin n) : (p : ProtoCoalition m) → Set where
  empty-coalition-agrees : CoalitionAgrees votes a b empty
  
  cons-coalition-agrees  : (p : ProtoCoalition m) 
               → (idx : ℕ) 
               → (m>idx : m ℕ.> idx) 
               → P (Get m n idx n>1 m>idx votes) a b 
               → CoalitionAgrees votes a b p
               --------------------------------------------------------
               → CoalitionAgrees votes a b (c-cons idx m>idx p)

data Disjoint (m : ℕ) : (p1 p2 : ProtoCoalition m)
                      → Set where

  l-empty-disjoint : (p2 : ProtoCoalition m)
                   -------------------------
                   → Disjoint m empty p2

  r-empty-disjoint : (p1 : ProtoCoalition m)
                   -------------------------
                   → Disjoint m p1 empty
  
  l-cons-disjoint : (p1 p2 : ProtoCoalition m) 
                  → (i : ℕ)
                  → (m>i : m ℕ.> i)
                  → ¬ (InCoalition m i p2)
                  → Disjoint m p1 p2
                  → Disjoint m (c-cons i m>i p1) p2

  r-cons-disjoint : (p1 p2 : ProtoCoalition m) 
                  → (i : ℕ)
                  → (m>i : m ℕ.> i)
                  → ¬ (InCoalition m i p1)
                  → Disjoint m p1 p2
                  → Disjoint m p1 (c-cons i m>i p2)

data Complete : (m : ℕ) → (p1 p2 : ProtoCoalition m) → Set where

  empty-complete  : Complete 1 empty empty

  l-cons-complete : (m : ℕ) 
                  → (p1 p2 : ProtoCoalition m) 
                  → Complete (suc m) (c-cons m (s≤s (ℕProp.≤-reflexive Eq.refl)) (Lift p1)) (Lift p2)
  
  r-cons-complete : (m : ℕ) 
                  → (p1 p2 : ProtoCoalition m) 
                  → Complete (suc m) (Lift p1) (c-cons m (s≤s (ℕProp.≤-reflexive Eq.refl)) (Lift p2))

record Split-Coalitions {m : ℕ} (p1 p2 : ProtoCoalition m) : Set where
  field
    coalition-1 : Coalition m p1
    coalition-2 : Coalition m p2
    disj        : Disjoint m p1 p2
    comp        : Complete m p1 p2
