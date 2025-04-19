{-# OPTIONS --rewriting #-}
module ArrowWorking where

open import Voter
open WeakPreference
open Preference
open StrictPreference

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Votes 
open import Election
open SWF

open import Coalition
open import Decisive
open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Vec
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; ∃)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Nat.Properties using (+-suc)

private
  variable
    n : ℕ
    n>2 : n ℕ.> 2
    result : {m : ℕ} → Votes n n>2 m → Fin n → Fin n → Set

LemmaOne : {m : ℕ} 
         → (v : Votes n n>2 m) 
         → (SWF result)
         → Decisive (Whole m) v result
LemmaOne {m = m} v swf a b ca = Pareto swf v a b (helper m v a b ca) where
  helper : (m : ℕ) 
         → (v : Votes n n>2 m) 
         → (a b : Fin n) 
         → CoalitionAgrees a b (Whole m) v 
         → ElectionAgrees v a b
  helper .0 [] a b c = tt
  helper (suc m) (x ∷ v) a b (true-agrees .(Whole m) .v c .x agrees) = 
    agrees , (helper m v a b c)

Decisive-x>x : {m : ℕ}
             → (v : Votes n n>2 m) 
             → (c : NonEmptyCoalition m)
             → (a b : Fin n)
             → (a ≡ b)
             → (CoalitionAgrees a b (Unwrap c) v)
             → ⊥
Decisive-x>x v c a b a≡b ca = ⊥-elim (helper v c a b a≡b ca)
  where
    helper : {m n : ℕ} → {n>2 : n ℕ.> 2} 
           → (v : Votes n n>2 m) 
           → (c : NonEmptyCoalition m) 
           → (a b : Fin n) 
           → (a ≡ b) 
           → (CoalitionAgrees a b (Unwrap c) v)
           → ⊥
    helper (p ∷ v) (.true ∷ c , _) a b a≡b 
      (true-agrees .c .v ca .p aPb) = ⊥-elim (aPb (R-refl p b a (Eq.sym a≡b)))
    helper (p ∷ v) (.(false ∷ c) , fst) a b a≡b 
      (false-agrees c .v ca .p) = helper v (c , fst) a b a≡b ca

FreshCandidate : (n : ℕ) 
               → (n>2 : n ℕ.> 2) 
               → (a b : Fin n) 
               → Σ (Fin n) λ c → ¬ (a ≡ c) × ¬ (b ≡ c)
FreshCandidate (suc zero) (s≤s ()) a b
FreshCandidate (suc (suc zero)) (s≤s (s≤s ())) a b
FreshCandidate (suc (suc (suc n))) n>2 zero zero 
  = (suc zero) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 zero (suc zero) 
  = (suc (suc zero)) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 zero (suc (suc b)) 
  = (suc zero) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc zero) zero 
  = (suc (suc zero)) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc a) (suc b) 
  = zero , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc (suc a)) zero 
  = (suc zero) , ((λ {()}) , (λ {()}))

LemmaTwoSimilar : {m : ℕ}
                → (c : Coalition m) 
                → (v : Votes n n>2 m) 
                → (x y z : Fin n)
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z)
                → (CoalitionAgrees y x (InverseCoalition c) v)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n n>2 m) 
                  λ v' → ((CoalitionAgrees x y c v') 
                       ×  (CoalitionAgrees y x (InverseCoalition c) v')
                       ×  (ElectionAgrees v' y z))
LemmaTwoSimilar [] [] x y z ¬x≡z ¬y≡z inv-y>x ca-x>y = 
  [] , (empty-coalition-agrees , empty-coalition-agrees , tt)
LemmaTwoSimilar (c ∷ c-rem) (p ∷ v) x y z ¬x≡z ¬y≡z
  (false-agrees inv .v inv-y>x .p)
  (true-agrees .c-rem .v ca-x>y .p xPy)
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z inv-y>x ca-x>y
... | v' , c'-x>y , inv'-y>x , ea-y>z 
  with Alter-First p y 
... | _ , p' , p'-y-first , p'-sim-non-y = (p' ∷ v') 
    , true-agrees c-rem v' c'-x>y p' x>y
    , false-agrees inv v' inv'-y>x p'
    , p'-y-first z (λ z≡y → ¬y≡z (Eq.sym z≡y)) , ea-y>z
      where 
        x>y : P p' x y
        x>y = {!   !}
LemmaTwoSimilar (c ∷ c-rem) (p ∷ v) x y z ¬x≡z ¬y≡z 
  (true-agrees inv .v inv-y>x .p yPx)
  (false-agrees .c-rem .v ca-x>y .p)
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z inv-y>x ca-x>y
... | v' , c'-x>y , inv'-y>x , ea-y>z 
  with Alter-Last p z
... | _ , p' , p'-z-last , p'-sim-non-z = (p' ∷ v') 
    , false-agrees c-rem v' c'-x>y p'
    , true-agrees inv v' inv'-y>x p' y>x
    , (p'-z-last y ¬y≡z , ea-y>z)
    where
        y>x : P p' y x 
        y>x = {!   !} 
LemmaTwo : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)         
         → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                 → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                 → result v' x y)
         → (CoalitionAgrees x z (Unwrap c) v)
         ------------------------------
         → result v x z
LemmaTwo {result = result} c v swf x y z dec-x>y ca-x>z = 
  BinaryIIA swf v {!   !} x z {!   !}
    (Transitive swf {!   !} x y z 
      (dec-x>y {!   !} {!   !} {!   !})
      (Pareto swf {!   !} y z {!   !})) 
{-
CorollaryOne : {m : ℕ} 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n n>2 m)
             → SWF result
             → (x y w : Fin n) 
             → CoalitionAgrees x y (Unwrap c) v
             → (CoalitionAgrees y x (InverseCoalition (Unwrap c)) v) 
             → result v x y
             → CoalitionAgrees x w (Unwrap c) v
             ------------------------------
             → result v x w
CorollaryOne {n} {n>2} c v swf x y w ca-x>y in-ca-y>x swfx>y ca-x>w 
  with x Fin.≟ w
... | true  because ofʸ  x≡w = ⊥-elim (Decisive-x>x v c x w x≡w ca-x>w)
... | false because ofⁿ ¬x≡w with y Fin.≟ w
... | false because ofⁿ ¬y≡w = 
  LemmaTwo c v swf x y w ¬x≡w ¬y≡w in-ca-y>x ca-x>y swfx>y ca-x>w 
... | true  because ofʸ  y≡w rewrite y≡w = swfx>y
-}
LemmaThree : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)
         → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                 → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                 → result v' x y)
         → CoalitionAgrees z y (Unwrap c) v
         ------------------------------
         → result v z y
LemmaThree c v swf x y z dec-x>y ca-z>y = 
  BinaryIIA swf v {!   !} z y {!   !}
    (Transitive swf {!   !} z x y
      {!   !}
      (dec-x>y {!   !} {!   !} {!   !})) 

LemmaFour : {m : ℕ}
          → (c : NonEmptyCoalition m)
          → (v : Votes n n>2 m)
          → SWF result
          → (x y : Fin n)
          → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                  → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                  → result v' x y)
          → Decisive (Unwrap c) v result
LemmaFour c v swf x y dec a b ca-a>b with LemmaTwo c v swf x y b (λ v' ca-x>y inv-y>x → dec v' ca-x>y inv-y>x)
... | f with LemmaThree c v swf x y a (λ v' ca-x>y inv-y>x → dec v' ca-x>y inv-y>x) 
... | g = {!   !}

LemmaFive' : (m : ℕ)
          → (SWF result)
          → Σ ℕ λ n → 
              Σ (Coalition m) λ c → 
                ∀ v → (Decisive c v result)
                    × (MembersCount c ≡ n) 
                    × ¬ (Σ ℕ λ n' → 
                           Σ (Coalition m) λ c' → 
                             (∀ v → (Decisive c v result))
                             × (MembersCount c ≡ n')
                             × (n' ℕ.< n))
LemmaFive' zero swf = 0 , [] , λ {[] → (λ a b _ → Pareto swf [] a b tt) 
                                    , refl 
                                    , (λ {(_ , _ , ())})}
LemmaFive' (suc m) swf = {!   !} 

LemmaFive : {m s : ℕ}
         → (c : Coalition m) 
         → (MembersCount c ≡ (suc s))
         → (x y : Fin n)
         → (∀ v' → CoalitionAgrees x y c v'
                 → result v' x y)
         → SWF result
         → (v : Votes n n>2 m) 
         → Dictator v result
LemmaFive {n} {s≤s (s≤s n>2)} {m = zero} [] mc x y _ swf v' = 
  ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
LemmaFive {s = zero} c mc x y dec swf v = {!   !}
LemmaFive {n} {n>2} {m = suc m} {s = suc s'} c mc x y dec-x>y swf v
  with FreshCandidate n n>2 x y 
... | z , ¬x≡z , ¬y≡z = {!   !} ,  
    LemmaFour {!   !} v swf z y 
      λ v' c-z>y inv-y>z → LemmaThree {!   !} v' swf x y z 
        (λ v'' d-x>y rem-y>x → 
        Transitive swf {!   !} x z y 
          (BinaryIIA swf v'' {!   !} x z {!   !} 
            (Transitive swf {!   !} x y z 
              (dec-x>y {!   !} {!   !}) 
              (Pareto swf {!   !} y z {!   !}))) 
          (BinaryIIA swf v'' {!   !} z y {!   !} 
            (Transitive swf {!   !} z x y 
              (Pareto swf {!   !} z x {!   !}) 
              (dec-x>y {!   !} {!   !})))) 
          c-z>y
  where
    LemmaFiveAlter : (v : Votes n n>2 m)
                   → (x y z : Fin n)
                   → (c c' : Coalition m)
                   → Σ (Votes n n>2 m)
                      λ v' → Similar m z y (Zipped n>2 z y v v')
ArrowsTheorem : {m : ℕ}
              → (v : Votes n n>2 m)
              → SWF result
              → Dictator v result       
ArrowsTheorem {n} {s≤s (s≤s n>2)} {m = zero} [] swf 
  = ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
ArrowsTheorem {n} {s≤s (s≤s n>2)} {m = (suc m)} v swf = 
  LemmaFive {s = (suc m)} (Whole (suc m)) {!   !} zero (suc zero) 
    (λ v' whole-agrees → LemmaOne v' swf zero (suc zero) whole-agrees)
    swf v