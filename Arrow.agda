{-# OPTIONS --rewriting #-}
module Arrow where

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
LemmaOne {m = m} v swf a b ca = SWF.Pareto swf v a b (helper m v a b ca) where
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
                → (CoalitionAgrees x y c v)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n n>2 m) 
                  λ v' → (Similar m x z (Zipped n>2 x z v v')  
                       × (Similar m x y (Zipped n>2 x y v' v)
                       ×  ElectionAgrees v' y z))
LemmaTwoSimilar [] [] x y z ¬x≡z ¬y≡z ea-x>y ca-x>y ca-y>z = 
  [] , (tt , tt , tt)
LemmaTwoSimilar c (p ∷ v) x y z ¬x≡z ¬y≡z
  (true-agrees inv-c-rem .v inv-y>x .p yPx) 
  (false-agrees c-rem .v ca-x>y .p) 
  (false-agrees c-rem .v ca-x>z .p)
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z inv-y>x ca-x>y ca-x>z
... | new-v , sim-x-z , sim-x-y , ea-y>z 
  with Alter-First p y 
... | _ , p' , p'-y-first , p'-sim-non-y = (p' ∷ new-v) 
    , ((p-x-z-sim , {!   !}) , sim-x-z) 
    , (({!   !} , {!   !}) , sim-x-y) 
    , p'-y-first z (λ z≡y → ¬y≡z (Eq.sym z≡y)) , ea-y>z
      where 
        ¬x≡y : ¬ x ≡ y 
        ¬x≡y x≡y = P↛≡ {v = p} yPx (Eq.sym x≡y)
        
        p-x-z-sim : P→Bool p x z ≡ P→Bool p' x z
        p-x-z-sim with p'-sim-non-y z x (λ z≡y → ¬y≡z (Eq.sym z≡y)) ¬x≡y 
        ... | R→R' , R'→R with R-dec p z x | R-dec p' z x
        ... | inj₁ zRx | inj₁ zR'x = refl
        ... | inj₁ zRx | inj₂ xP'z = ⊥-elim (xP'z (R→R' zRx))
        ... | inj₂ xPz | inj₁ zR'x = ⊥-elim (xPz (R'→R zR'x))
        ... | inj₂ xPz | inj₂ xP'z = refl
        
LemmaTwoSimilar c (p ∷ v) x y z ¬x≡z ¬y≡z 
  (false-agrees inv-c-rem .v inv-y>x .p)
  (true-agrees c-rem .v ca-x>y .p xPy)
  (true-agrees c-rem .v ca-x>z .p xPz)
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z inv-y>x ca-x>y ca-x>z
... | new-v , sim-x-z , sim-x-y , ea-y>z   
  with Alter-Last p z
... | _ , p' , p'-z-last , p'-sim-non-z = (p' ∷ new-v) 
    , ((sim-xPz , sim-zPx) , sim-x-z) 
    , (({!   !} , {!   !}) , sim-x-y) 
    , p'-z-last y ¬y≡z , ea-y>z
      where
        ¬x≡y : ¬ x ≡ y 
        ¬x≡y = P↛≡ {v = p} xPy

        sim-xPz : P→Bool p x z ≡ P→Bool p' x z
        sim-xPz with R-dec p z x
        ... | inj₁ zRx = ⊥-elim (xPz zRx)
        ... | inj₂ xPx with R-dec p' z x
        ... | inj₁ zR'x = ⊥-elim (p'-z-last x ¬x≡z zR'x)
        ... | inj₂ zP'x = refl

        sim-zPx : P→Bool p z x ≡ P→Bool p' z x
        sim-zPx with R-dec p' x z | R-dec p x z
        ... | inj₁ _ | inj₁ _ = refl
        ... | _ | inj₂ zPx = ⊥-elim (zPx (P→R {v = p} xPz))
        ... | inj₂ zP'x | _ = ⊥-elim (zP'x (P→R {v = p'} (p'-z-last x ¬x≡z)))

LemmaTwo : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)         
         → ¬ (x ≡ z) 
         → ¬ (y ≡ z) 
         → (CoalitionAgrees y x (InverseCoalition (Unwrap c)) v)
         → (CoalitionAgrees x y (Unwrap c) v)
         → result v x y
         → (CoalitionAgrees x z (Unwrap c) v)
         ------------------------------
         → result v x z
LemmaTwo {result = result} c v swf x y z ¬x≡z ¬y≡z inv-y>x ca-x>y res-x>y ca-x>z
  with LemmaTwoSimilar (Unwrap c) v x y z ¬x≡z ¬y≡z inv-y>x ca-x>y ca-x>z
... | new-v , sim-x-z , sim-x-y , ea-y>z = 
  BinaryIIA swf v new-v x z sim-x-z 
    (Transitive swf new-v x y z 
      (BinaryIIA swf new-v v x y sim-x-y res-x>y)
      (Pareto swf new-v y z ea-y>z)) 

LemmaThree : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)
         → ¬ (x ≡ z)
         → ¬ (y ≡ z) 
         → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v
         → CoalitionAgrees x y (Unwrap c) v
         → result v x y
         → CoalitionAgrees z y (Unwrap c) v
         ------------------------------
         → result v z y
LemmaThree c v swf x y z ¬x≡z ¬y≡z inv-y>x ca-x>y res-x>y ca-z>y = 
  BinaryIIA swf v {!   !} z y {!   !}
    (Transitive swf {!   !} z x y
      {!   !}
      {!   !}) 

LemmaFour : {m : ℕ}
          → (c : NonEmptyCoalition m)
          → (v : Votes n n>2 m)
          → (x y : Fin n)
          → SWF result
          → (CoalitionAgrees x y (Unwrap c) v)
          → (CoalitionAgrees y x (InverseCoalition (Unwrap c)) v)
          → result v x y
          → Decisive (Unwrap c) v result
LemmaFour c v x y swf ca-x>y inv-y>x res-x>y a b ca-a>b 
  with x Fin.≟ a | y Fin.≟ b 
... | false because ofⁿ ¬x≡a | false because ofⁿ ¬y≡b =
  BinaryIIA swf v {!  v' !} a b {!   !} --sim-a-b
    (Transitive swf {! v'  !} a x b 
      (Pareto swf {! v'  !} a x {!   !}) -- a>x
      (Transitive swf {! v'  !} x y b 
        (BinaryIIA swf {!  v' !} v x y {!   !} res-x>y) --sim-x>y
        (Pareto swf {!  v' !} y b {!   !}))) -- y>b
... | true because ofʸ x≡a | false because ofⁿ ¬y≡b rewrite x≡a = 
    LemmaTwo c v swf a y b {!   !} ¬y≡b inv-y>x ca-x>y res-x>y ca-a>b
... | false because ofⁿ ¬x≡a | true because ofʸ y≡b rewrite y≡b = 
    LemmaThree c v swf x b a ¬x≡a {!   !} inv-y>x ca-x>y res-x>y ca-a>b
... | true because ofʸ x≡a | true because ofʸ y≡b rewrite x≡a | y≡b = res-x>y

LemmaFive : {m s : ℕ}
          → (c : Coalition m)
          → (v : Votes n n>2 m)
          → SWF result
          → Decisive c v result
          → (x y z a b : Fin n)
          → Σ (Votes n n>2 m) λ v' → 
              Σ (SingletonCoalition m) λ sc →
                  CoalitionAgrees z y {!   !} v' 
                × CoalitionAgrees y z {!   !} v' 
                × Similar m x y (Zipped n>2 x y v' v)
                × Similar m z x (Zipped n>2 z x v' v)
                × Similar m a b (Zipped n>2 a b v v')
LemmaFive c v swf dec x y z a b = {!   !}

LemmaSix : {m s : ℕ}
         → (c : Coalition m) 
         → (MembersCount c ≡ (suc s))
         → (v : Votes n n>2 m)
         → Decisive c v result
         → SWF result
         → (x y : Fin n)
         → result v x y
         → Dictator v result
LemmaSix {n} {s≤s (s≤s n>2)} {m = zero} [] mc [] _ swf _ = 
  ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
LemmaSix {s = zero} c mc v dec swf x y res-x>y = (c , mc) , dec
LemmaSix {n} {n>2} {m = suc m} {s = suc s'} c mc v dec swf x y res-x>y
  with FreshCandidate n n>2 x y 
... | z , ¬x≡z , ¬y≡z 
  with Complete swf v x z ¬x≡z
... | inj₁ xPz = {!   !}

-- similar for z and x , x and y, and a and b, have ca z=x>y and inv y>x=z, gen proof of x>y
... | inj₂ zPx = {!   !} , λ a b ca-a>b → BinaryIIA swf v {!   !} a b {!   !}
    (LemmaFour {!   !} {!   !} z y swf {!   !} {!   !} 
      (LemmaThree {!   !} {!   !} swf x y z ¬x≡z ¬y≡z {!   !} {!   !} {!   !} {!   !}) 
     a b {!   !})

ArrowsTheorem : {m : ℕ}
              → (v : Votes n n>2 m)
              → SWF result
              → Dictator v result       
ArrowsTheorem {n} {s≤s (s≤s n>2)} {m = zero} [] swf 
  = ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
ArrowsTheorem {n} {s≤s (s≤s n>2)} {m = (suc m)} v swf 
  with (SWF.Complete swf v zero (suc zero) λ {()})
... | inj₁ 0P1 = 
  LemmaSix {s = m} (Whole (suc m)) {!   !} v 
    (LemmaOne v swf) swf zero (suc zero) 0P1
... | inj₂ 1P0 =
  LemmaSix {s = m} (Whole (suc m)) {!   !} v 
    (LemmaOne v swf) swf (suc zero) zero 1P0 