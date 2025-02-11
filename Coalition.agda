module Coalition where

open import Votes using (Votes; Get; _∷_)
open import Voter
open WeakPreference using (Preference; R→Bool)
open StrictPreference using (P; P→Bool)
open PreferenceEquality
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕProp using (≤∧≢⇒<; <⇒≤; ≤-reflexive; ≤⇒≯ ; n<1+n; >⇒≢ )
open import Data.Fin as Fin hiding (_+_)
open import Data.Product using (Σ; _×_; _,_; proj₂; proj₁)
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
                → Increasing m (c-cons i m>i pc)
                -------------------------------------------------
                → Increasing m (c-cons i' m>i' (c-cons i m>i pc))

LiftIncreasing : {m : ℕ} → (p : ProtoCoalition m) → Increasing m p → Increasing (suc m) (Lift p)
LiftIncreasing p empty-inc = empty-inc
LiftIncreasing p (singleton-inc i m>i) = singleton-inc i (s≤s (ℕProp.<⇒≤ m>i))
LiftIncreasing p (cons-inc i i' m>i' m>i x pc inc) = cons-inc i i' (s≤s (ℕProp.<⇒≤ m>i')) (s≤s (ℕProp.<⇒≤ m>i)) x (Lift pc) (LiftIncreasing (c-cons i m>i pc) inc)

data UniqueEntries (m : ℕ) : ProtoCoalition m → Set where
  empty-uq-entries : UniqueEntries m empty

  cons-uq-entries  : (i : ℕ)
                   → (m>i : m ℕ.> i)
                   → (pc : ProtoCoalition m)
                   → ¬ InCoalition m i pc
                   → UniqueEntries m pc
                   -----------------------------------
                   → UniqueEntries m (c-cons i m>i pc)

¬mInCoalitionLift : {m : ℕ} → (p : ProtoCoalition m) → ¬ (InCoalition (suc m) m (Lift p))
¬mInCoalitionLift (c-cons idx (s≤s {n = n} x) p) (in-coalition-head .(suc n) .(s≤s (ℕProp.<⇒≤ (s≤s x))) .(Lift p)) = ℕProp.≤⇒≯ x (s≤s (ℕProp.≤-reflexive Eq.refl))
¬mInCoalitionLift (c-cons idx x p) (in-coalition-tail .idx _ .(s≤s (ℕProp.<⇒≤ x)) .(Lift p) in-coalition) = ¬mInCoalitionLift p in-coalition

¬mInCoalitionLift' : {m : ℕ} → (p : ProtoCoalition m) → ¬ (InCoalition (suc (suc m)) m (Lift (Lift p)))
¬mInCoalitionLift' (c-cons idx (s≤s x) p) (in-coalition-head .(suc _) .(s≤s (ℕProp.<⇒≤ (s≤s (ℕProp.<⇒≤ (s≤s x))))) .(Lift (Lift p))) = ℕProp.≤⇒≯ x (s≤s (ℕProp.≤-reflexive Eq.refl))
¬mInCoalitionLift' (c-cons idx x p) (in-coalition-tail .idx _ .(s≤s (ℕProp.<⇒≤ (s≤s (ℕProp.<⇒≤ x)))) .(Lift (Lift p)) coal) = ¬mInCoalitionLift' p coal

idxInCoalitionLift : {m idx : ℕ} → (p : ProtoCoalition m) → InCoalition m idx p → InCoalition (suc m) idx (Lift p)
idxInCoalitionLift (c-cons idx x p) (in-coalition-head .idx .x .p) = in-coalition-head idx (s≤s (ℕProp.<⇒≤ x)) (Lift p)
idxInCoalitionLift (c-cons idx x p) (in-coalition-tail .idx m .x .p in-c) = in-coalition-tail idx m (s≤s (ℕProp.<⇒≤ x)) (Lift p) (idxInCoalitionLift p in-c)

idxInCoalitionUnlift : {m idx : ℕ} → (p : ProtoCoalition m) → InCoalition (suc m) idx (Lift p) → InCoalition m idx p 
idxInCoalitionUnlift (c-cons idx x p) (in-coalition-head .idx .(s≤s (ℕProp.<⇒≤ x)) .(Lift p)) = in-coalition-head idx x p
idxInCoalitionUnlift (c-cons idx x p) (in-coalition-tail .idx m .(s≤s (ℕProp.<⇒≤ x)) .(Lift p) in-coalition) = in-coalition-tail idx m x p (idxInCoalitionUnlift p in-coalition)

LiftUnique : {m : ℕ} → (p : ProtoCoalition m) → UniqueEntries m p → UniqueEntries (suc m) (Lift p)
LiftUnique empty uq = empty-uq-entries
LiftUnique (c-cons idx x p) (cons-uq-entries .idx .x .p ¬in-coalition uq) = cons-uq-entries idx (s≤s (ℕProp.<⇒≤ x)) (Lift p) (λ x₁ → ¬in-coalition (idxInCoalitionUnlift p x₁)) (LiftUnique p uq)

ReverseLiftUnique : {m : ℕ} → (p : ProtoCoalition m) → UniqueEntries (suc m) (Lift p) → UniqueEntries m p
ReverseLiftUnique empty uq = empty-uq-entries
ReverseLiftUnique (c-cons idx x p) (cons-uq-entries .idx .(s≤s (ℕProp.<⇒≤ x)) .(Lift p) ¬in-tail uq) = cons-uq-entries idx x p (λ in-tail → ¬in-tail (idxInCoalitionLift p in-tail)) (ReverseLiftUnique p uq)

record Coalition (m : ℕ) (p : ProtoCoalition m) : Set where
  field
    inc : Increasing m p
    uq-entries : UniqueEntries m p

EmptyCoalition : (m : ℕ) → Coalition m empty
EmptyCoalition m = record { inc = empty-inc ; uq-entries = empty-uq-entries } 

TailIsUnique : {m i : ℕ} → (sm>i : (suc m) ℕ.> i) → (p : ProtoCoalition m) → UniqueEntries (suc m) (c-cons i sm>i (Lift p)) → UniqueEntries m p
TailIsUnique sm>i empty uq = empty-uq-entries
TailIsUnique sm>i (c-cons idx x p) (cons-uq-entries h .sm>i .(Lift (c-cons idx x p)) ¬in-tail (cons-uq-entries .idx .(s≤s (ℕProp.<⇒≤ x)) .(Lift p) ¬in-tail' uq)) = cons-uq-entries idx x p (λ in-tail → ¬in-tail'  (idxInCoalitionLift p in-tail)) (TailIsUnique sm>i p (cons-uq-entries h sm>i (Lift p) (λ h-in-tail → ¬in-tail (in-coalition-tail idx h (s≤s (ℕProp.<⇒≤ x)) (Lift p) h-in-tail)) uq))

data CoalitionAgrees {m n : ℕ} {n>1 : n ℕ.> 1} (votes : Votes n n>1 m) (a b : Fin n) : (p : ProtoCoalition m) → Set where
  empty-coalition-agrees : CoalitionAgrees votes a b empty
  
  cons-coalition-agrees  : (p : ProtoCoalition m) 
               → (idx : ℕ) 
               → (m>idx : m ℕ.> idx) 
               → P (proj₂ (Get m idx m>idx votes)) a b 
               → CoalitionAgrees votes a b p
               ------------------------------------------------
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

LiftDisjoint : {m : ℕ} → (p1 p2 : ProtoCoalition m) → Disjoint m p1 p2 → Disjoint (suc m) (Lift p1) (Lift p2)
LiftDisjoint p1 p2 (l-empty-disjoint .p2) = l-empty-disjoint (Lift p2)
LiftDisjoint p1 p2 (r-empty-disjoint .p1) = r-empty-disjoint (Lift p1) 
LiftDisjoint p1 p2 (l-cons-disjoint p3 .p2 i m>i ¬in-tail disj) = l-cons-disjoint (Lift p3) (Lift p2) i (s≤s (ℕProp.<⇒≤ m>i)) (λ in-tail → ¬in-tail (idxInCoalitionUnlift p2 in-tail)) (LiftDisjoint p3 p2 disj)
LiftDisjoint p1 p2 (r-cons-disjoint .p1 p3 i m>i ¬in-tail disj) = r-cons-disjoint (Lift p1) (Lift p3) i (s≤s (ℕProp.<⇒≤ m>i)) (λ in-tail → ¬in-tail (idxInCoalitionUnlift p1 in-tail)) (LiftDisjoint p1 p3 disj)
{-
UnliftDisjoint : {m : ℕ} → (p1 p2 : ProtoCoalition m) → Disjoint (suc m) (Lift p1) (Lift p2) → Disjoint m p1 p2
UnliftDisjoint empty p2 disj = l-empty-disjoint p2
UnliftDisjoint p1 empty disj = r-empty-disjoint p1
UnliftDisjoint (c-cons idx x p1) (c-cons idx₁ x₁ p2) (l-cons-disjoint .(Lift p1) .(Lift (c-cons idx₁ x₁ p2)) .idx .(s≤s (ℕProp.<⇒≤ x)) x₂ disj) = l-cons-disjoint p1 (c-cons idx₁ x₁ p2) idx x {!   !} {!   !}
UnliftDisjoint (c-cons idx x p1) (c-cons idx₁ x₁ p2) (r-cons-disjoint .(Lift (c-cons idx x p1)) .(Lift p2) .idx₁ .(s≤s (ℕProp.<⇒≤ x₁)) x₂ disj) = r-cons-disjoint (c-cons idx x p1) p2 idx₁ x₁ {!   !} {!   !}

TailIsDisjoint-l : {m i : ℕ} → (sm>i : m ℕ.> i) → (p1 p2 : ProtoCoalition m) → Disjoint m (c-cons i sm>i p1) p2 → Disjoint m p1 p2
TailIsDisjoint-r : {m i : ℕ} → (sm>i : m ℕ.> i) → (p1 p2 : ProtoCoalition m) → Disjoint m p1 (c-cons i sm>i p2) → Disjoint m p1 p2

TailIsDisjoint-l m>i empty p2 disj = l-empty-disjoint p2
TailIsDisjoint-l m>i p1 empty disj = r-empty-disjoint p1
TailIsDisjoint-l m>i p1 p2 (l-cons-disjoint .p1 .p2 _ .m>i x disj) = disj
TailIsDisjoint-l m>i p1 p2 (r-cons-disjoint .(c-cons _ m>i p1) p3 i m>i₁ ¬in-tail disj) = r-cons-disjoint p1 p3 i m>i₁ (λ in-tail → ¬in-tail (in-coalition-tail {!   !} i m>i p1 in-tail)) (TailIsDisjoint-l m>i p1 p3 disj) 

TailIsDisjoint-r m>i empty p2 disj = l-empty-disjoint p2
TailIsDisjoint-r m>i p1 empty disj = r-empty-disjoint p1
TailIsDisjoint-r m>i p1 p2 (l-cons-disjoint p3 .(c-cons _ m>i p2) i m>i₁ x disj) = {!   !}
TailIsDisjoint-r m>i p1 p2 (r-cons-disjoint .p1 .p2 _ .m>i x disj) = {!   !}

DisjointComm : {m : ℕ} → (p1 p2 : ProtoCoalition m) → Disjoint m p1 p2 → Disjoint m p2 p1
DisjointComm empty p2 disj = r-empty-disjoint p2
DisjointComm p1 empty disj = l-empty-disjoint p1
DisjointComm p1 p2 (l-cons-disjoint p3 .p2 i m>i x disj) = r-cons-disjoint p2 p3 i m>i x (DisjointComm p3 p2 disj)
DisjointComm p1 p2 (r-cons-disjoint .p1 p3 i m>i x disj) = {!   !}
-}

data Complete : (m : ℕ) → (p1 p2 : ProtoCoalition m) → Set where

  empty-complete  : Complete 0 empty empty

  l-cons-complete : (m : ℕ) 
                  → (p1 p2 : ProtoCoalition m)
                  → Complete m p1 p2
                  → Complete (suc m) (c-cons m (s≤s (ℕProp.≤-reflexive Eq.refl)) (Lift p1)) (Lift p2)
  
  r-cons-complete : (m : ℕ) 
                  → (p1 p2 : ProtoCoalition m) 
                  → Complete m p1 p2
                  → Complete (suc m) (Lift p1) (c-cons m (s≤s (ℕProp.≤-reflexive Eq.refl)) (Lift p2))

record Split-Coalitions {m : ℕ} (p1 p2 : ProtoCoalition m) : Set where
  field
    coalition-1 : Coalition m p1
    coalition-2 : Coalition m p2
    disj        : Disjoint m p1 p2
    comp        : Complete m p1 p2

LiftCoalition : {m : ℕ} → (p : ProtoCoalition m) → (Coalition m p) → Coalition (suc m) (Lift p)
LiftCoalition {m = m} empty c = EmptyCoalition (suc m)
LiftCoalition (c-cons idx x p) record { inc = (singleton-inc .idx .x) ; uq-entries = uq-entries } = record { inc = singleton-inc idx (s≤s (ℕProp.<⇒≤ x)) ; uq-entries = LiftUnique (c-cons idx x p) uq-entries }
LiftCoalition (c-cons idx x p) record { inc = (cons-inc i .idx .x m>i x₁ pc inc) ; uq-entries = (cons-uq-entries .idx .x .(c-cons i m>i pc) ¬in-tail (cons-uq-entries .i .m>i .pc x₂ uq-entries)) } =  record { inc = cons-inc i idx (s≤s (ℕProp.<⇒≤ x)) (s≤s (ℕProp.<⇒≤ m>i)) x₁ (Lift pc) (LiftIncreasing p inc) ; uq-entries = cons-uq-entries idx (s≤s (ℕProp.<⇒≤ x)) (Lift p) (λ {(in-coalition-head .idx .(s≤s (ℕProp.<⇒≤ m>i)) .(Lift pc)) → ℕProp.>⇒≢ x₁ Eq.refl
                                                                                                                                                                                                                                                                                                                                                                                    ; (in-coalition-tail .i .idx .(s≤s (ℕProp.<⇒≤ m>i)) .(Lift pc) in-tail) → ¬in-tail (idxInCoalitionUnlift p (in-coalition-tail i idx (s≤s (ℕProp.<⇒≤ m>i)) (Lift pc) in-tail))}) (cons-uq-entries i (s≤s (ℕProp.<⇒≤ m>i)) (Lift pc) (λ in-lifted-tail → x₂ (idxInCoalitionUnlift pc in-lifted-tail)) (LiftUnique pc uq-entries)) } 
ExpandCoalition : (m : ℕ) → (p1 p2 : ProtoCoalition m) → Split-Coalitions p1 p2 → Split-Coalitions (c-cons m (ℕProp.n<1+n m) (Lift p1)) (Lift p2)
ExpandCoalition zero empty empty split = 
  record { coalition-1 = record { inc = singleton-inc 0 (s≤s z≤n)
                                ; uq-entries = cons-uq-entries 0 (s≤s z≤n) (Lift empty) (λ ()) empty-uq-entries} 
           ; coalition-2 = EmptyCoalition 1
           ; disj = l-cons-disjoint empty empty 0 (s≤s z≤n) (λ ()) (l-empty-disjoint empty) 
           ; comp = l-cons-complete 0 empty empty empty-complete } 
ExpandCoalition (suc m) empty p2 split = 
  record { coalition-1 = record { inc = singleton-inc (suc m) (s≤s (ℕProp.≤-reflexive Eq.refl)); uq-entries = cons-uq-entries (suc m) (s≤s (ℕProp.≤-reflexive Eq.refl)) empty (λ ()) empty-uq-entries }
         ; coalition-2 = LiftCoalition p2 (Split-Coalitions.coalition-2 split) 
         ; disj = l-cons-disjoint (Lift empty) (Lift p2) (suc m) (s≤s (ℕProp.≤-reflexive Eq.refl)) (¬mInCoalitionLift p2) (LiftDisjoint empty p2 (Split-Coalitions.disj split)) 
         ; comp = l-cons-complete (suc m) empty p2 (Split-Coalitions.comp split) } 
ExpandCoalition (suc m) (c-cons idx x p1) p2 split = 
  record { coalition-1 = record { inc = cons-inc idx (suc m) (ℕProp.n<1+n (suc m)) (s≤s (ℕProp.<⇒≤ x)) x (Lift p1) (LiftIncreasing (c-cons idx x p1) (Coalition.inc (Split-Coalitions.coalition-1 split)))
                                  ; uq-entries = cons-uq-entries (suc m) (ℕProp.n<1+n (suc m)) (Lift (c-cons idx x p1)) (¬mInCoalitionLift (c-cons idx x p1)) (LiftUnique (c-cons idx x p1) (Coalition.uq-entries (Split-Coalitions.coalition-1 split))) }
         ; coalition-2 = LiftCoalition p2 (Split-Coalitions.coalition-2 split)
         ; disj = l-cons-disjoint (Lift (c-cons idx x p1)) (Lift p2) (suc m) (s≤s (ℕProp.≤-reflexive Eq.refl)) (¬mInCoalitionLift p2) (LiftDisjoint (c-cons idx x p1) p2 (Split-Coalitions.disj split))
         ; comp = l-cons-complete (suc m) (c-cons idx x p1) p2 (Split-Coalitions.comp split) } 
         
CoalitionOfWhole : (m : ℕ) → Σ (ProtoCoalition m) λ p → Split-Coalitions p empty
CoalitionOfWhole zero = empty , (record
   { coalition-1 = EmptyCoalition ℕ.zero ; coalition-2 = EmptyCoalition ℕ.zero ; disj = l-empty-disjoint empty ; comp = empty-complete }) 
CoalitionOfWhole (suc m) with CoalitionOfWhole m    
... | fst , snd = c-cons m (ℕProp.n<1+n m) (Lift fst) , ExpandCoalition m fst empty snd 