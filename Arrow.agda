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

-- the coalition of the whole is decisive

-- do william naming thingy

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
  helper (suc m) (x ∷ v) a b (true-agrees .(Whole m) .v c .x agrees) = agrees , (helper m v a b c)

Decisive-x>x : {m : ℕ}
             → (c : NonEmptyCoalition m)
             → (a b : Fin n)
             → (a ≡ b)
             → Decisive-a>b (Unwrap c) result a b 
Decisive-x>x c a b a≡b v ca = ⊥-elim (helper v c a b a≡b ca)
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


LemmaTwoSimilar : {m : ℕ}
                → (c : Coalition m) 
                → (v : Votes n n>2 m) 
                → (x y z : Fin n)
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n n>2 m) 
                  λ v' → (Similar m x z (Zipped n>2 x z v v')  
                       × (CoalitionAgrees x y c v')
                       ×  ElectionAgrees v' y z)
LemmaTwoSimilar [] [] x y z ¬x≡z ¬y≡z ca-x>y = [] , (tt , (empty-coalition-agrees , tt))
LemmaTwoSimilar c (p ∷ v) x y z ¬x≡z ¬y≡z (false-agrees c-rem .v ca-x>z .p) 
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z ca-x>z 
... | new-v , sim-x-z , ca-x>y , ea-y>z 
  with Alter-First p y 
... | _ , p' , p'-y-first , p'-sim-non-y = (p' ∷ new-v) 
    , (({!   !} , {!   !}) , sim-x-z)  
    , false-agrees c-rem new-v ca-x>y p' 
    , p'-y-first z (λ z≡y → ¬y≡z (Eq.sym z≡y)) , ea-y>z
LemmaTwoSimilar c (p ∷ v) x y z ¬x≡z ¬y≡z (true-agrees c-rem .v ca-x>z .p xPz) 
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z ca-x>z 
... | new-v , sim-x-z , ca-x>y , ea-y>z 
  with Alter-First p x 
... | _ , p' , p'-x-first , p'-sim-non-x
  with Alter-Last p z 
... | _ , p'' , p''-z-last , p''-sim -- x > y > z
    = (p'' ∷ new-v) 
    , (({!   !} , {!   !}) , sim-x-z) 
    , true-agrees c-rem new-v ca-x>y p'' {!   !} 
    , p''-z-last y ¬y≡z , ea-y>z

LemmaTwo : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)
         → ¬ (y ≡ z) 
         → Decisive-a>b (Unwrap c) result x y
         → (CoalitionAgrees x z (Unwrap c) v)
         ------------------------------
         → result v x z
LemmaTwo {result = result} c v swf x y z ¬y≡z dec-x>y ca-x>z with x Fin.≟ z 
... | true because ofʸ x≡z = Decisive-x>x {result = result} c x z x≡z v ca-x>z
... | false because ofⁿ ¬x≡z 
  with LemmaTwoSimilar (Unwrap c) v x y z ¬x≡z ¬y≡z ca-x>z 
... | new-v , sim-x-z , ca-x>y , ea-y>z = 
  SWF.BinaryIIA swf v new-v x z sim-x-z 
    (SWF.Transitive swf new-v x y z 
      (dec-x>y new-v ca-x>y) 
      (SWF.Pareto swf new-v y z ea-y>z)) 

LemmaThree : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)
         → ¬ (x ≡ z) 
         → Decisive-a>b (Unwrap c) result x y
         → (CoalitionAgrees z y (Unwrap c) v)
         ------------------------------
         → result v z y
LemmaThree {result = result} c v swf x y z ¬x≡z dec-x>y ca-z>y with z Fin.≟ y
... | true because ofʸ z≡y = Decisive-x>x {result = result} c z y z≡y v ca-z>y
... | false because ofⁿ ¬z≡y = 
  SWF.BinaryIIA swf v {!   !} z y {!   !}
    (SWF.Transitive swf {!   !} z x y
      (SWF.Pareto swf {!   !} z x {!   !})
      (dec-x>y {!   !} {!   !}))  {-
  with LemmaTwoSimilar (Unwrap c) v x y z ¬x≡z ¬y≡z ca-x>z 
... | new-v , sim-x-z , ca-x>y , ea-y>z = 
  SWF.BinaryIIA swf v new-v x z sim-x-z 
    (SWF.Transitive swf new-v x y z 
      (dec-x>y new-v ca-x>y) 
      (SWF.Pareto swf new-v y z ea-y>z)) 
-}
LemmaFour : {m : ℕ}
          → (c : NonEmptyCoalition m)
          → (v : Votes n n>2 m)
          → (x y : Fin n)
          → SWF result
          → CoalitionAgrees x y (Unwrap c) v
          → (Decisive-a>b (Unwrap c) result x y)
          → Decisive (Unwrap c) v result
LemmaFour c v x y swf ca-x>y dec-x>y a b ca-a>b 
  with x Fin.≟ a | y Fin.≟ b 
... | false because ofⁿ ¬x≡a | false because ofⁿ ¬y≡b =
  SWF.BinaryIIA swf v {!  v' !} a b {!   !} --sim-a-b
    (SWF.Transitive swf {! v'  !} a x b 
      (SWF.Pareto swf {! v'  !} a x {!   !}) -- a>x
      (SWF.Transitive swf {! v'  !} x y b 
        (dec-x>y {! v'  !} ca-x>y) 
        (SWF.Pareto swf {!  v' !} y b {!   !}))) -- y>b
... | false because ofⁿ ¬x≡a | true because ofʸ y≡b rewrite y≡b = 
  LemmaThree c v swf x b a ¬x≡a dec-x>y ca-a>b
... | true because ofʸ x≡a | false because ofⁿ ¬y≡b rewrite x≡a = 
  LemmaTwo c v swf a y b ¬y≡b dec-x>y ca-a>b
... | true because ofʸ x≡a | true because ofʸ y≡b rewrite x≡a | y≡b 
  = dec-x>y v ca-a>b {-
  = SWF.BinaryIIA swf v {!  v' !} a b {!   !} --sim-a-b
    (SWF.Transitive swf {! v'  !} a x b 
      (SWF.Pareto swf {! v'  !} a x {!   !}) -- a>x
      (SWF.Transitive swf {! v'  !} x y b 
        (dec-x>y {! v'  !} ca-x>y) 
        (SWF.Pareto swf {!  v' !} y b {!   !}))) -- y>b
        -}
LemmaFive : 
{-
ArrowsTheorem : (m : ℕ) 
              → (ballots : Votes n n>2 m)
              → SWF Result
              → Dictator ballots Result        
ArrowsTheorem {n} {s≤s (s≤s n>2)} zero [] swf 
  = ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
ArrowsTheorem (suc m) ballots swf with LemmaFive ballots swf
... | pivot , dec-x>y
    = pivot , (λ a b pivot-a>b → LemmaFour (suc m) pivot ballots swf a b dec-x>y pivot-a>b)  
-}