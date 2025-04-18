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
    , ((p-x-z-sim , p-z-x-sim) , sim-x-z) 
    , ((p-x-y-sim , p-y-x-sim) , sim-x-y) 
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

        p-z-x-sim : P→Bool p z x ≡ P→Bool p' z x
        p-z-x-sim with p'-sim-non-y x z ¬x≡y (λ z≡y → ¬y≡z (Eq.sym z≡y)) 
        ... | R→R' , R'→R with R-dec p x z | R-dec p' x z
        ... | inj₁ xRz | inj₁ xR'z = refl
        ... | inj₁ xRz | inj₂ zP'x = ⊥-elim (zP'x (R→R' xRz))
        ... | inj₂ zPx | inj₁ xR'z = ⊥-elim (zPx (R'→R xR'z))
        ... | inj₂ zPx | inj₂ zP'z = refl

        p-x-y-sim : P→Bool p' x y ≡ P→Bool p x y
        p-x-y-sim with R-dec p y x | R-dec p' y x
        ... | inj₁ yRx | inj₁ yR'x = refl
        ... | _ | inj₂ xP'y = ⊥-elim (xP'y (P→R {v = p'} (p'-y-first x ¬x≡y)))
        ... | inj₂ xPy | _ = ⊥-elim (xPy (P→R {v = p} yPx))

        p-y-x-sim : P→Bool p' y x ≡ P→Bool p y x
        p-y-x-sim with R-dec p x y | R-dec p' x y
        ... | inj₁ xRy | _ = ⊥-elim (yPx xRy)
        ... | _ | inj₁ xR'y = ⊥-elim (p'-y-first x ¬x≡y xR'y)
        ... | inj₂ yPx | inj₂ yP'x = refl
        
LemmaTwoSimilar c (p ∷ v) x y z ¬x≡z ¬y≡z 
  (false-agrees inv-c-rem .v inv-y>x .p)
  (true-agrees c-rem .v ca-x>y .p xPy)
  (true-agrees c-rem .v ca-x>z .p xPz)
  with LemmaTwoSimilar c-rem v x y z ¬x≡z ¬y≡z inv-y>x ca-x>y ca-x>z
... | new-v , sim-x-z , sim-x-y , ea-y>z   
  with Alter-Last p z
... | _ , p' , p'-z-last , p'-sim-non-z = (p' ∷ new-v) 
    , ((sim-xPz , sim-zPx) , sim-x-z) 
    , ((p-x-y-sim , p-y-x-sim) , sim-x-y) 
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

        p-x-y-sim : P→Bool p' x y ≡ P→Bool p x y
        p-x-y-sim with p'-sim-non-z y x ¬y≡z ¬x≡z
        ... | R→R' , R'→R with R-dec p y x | R-dec p' y x
        ... | inj₁ yRx | _ = ⊥-elim (xPy yRx)
        ... | _ | inj₁ yR'x = ⊥-elim (xPy (R'→R yR'x))
        ... | inj₂ _ | inj₂ _ = refl

        p-y-x-sim : P→Bool p' y x ≡ P→Bool p y x
        p-y-x-sim with p'-sim-non-z y x ¬y≡z ¬x≡z
        ... | R→R' , R'→R with R-dec p x y | R-dec p' x y
        ... | inj₁ xRy | inj₁ xR'y = refl
        ... | _ | inj₂ yP'x = ⊥-elim (xPy (R'→R (P→R {v = p'} yP'x)))
        ... | inj₂ yPx | _ = ⊥-elim (xPy (P→R {v = p} yPx))

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

LemmaThree : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n n>2 m) 
         → SWF result
         → (x y z : Fin n)
         → ¬ (x ≡ z)
         → ¬ (y ≡ z)
         → CoalitionAgrees x y (Unwrap c) v 
         → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v
         → result v x y
         → CoalitionAgrees z y (Unwrap c) v
         ------------------------------
         → result v z y
LemmaThree c v swf x y z ¬x≡z ¬y≡z inv-y>x ca-x>y res-x>y ca-z>y = 
  BinaryIIA swf v {!   !} z y {!   !}
    (Transitive swf {!   !} z x y
      {!   !}
      {!   !}) 

CorollaryTwo : {m : ℕ} 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n n>2 m)
             → SWF result
             → (x y w : Fin n) 
             → CoalitionAgrees x y (Unwrap c) v
             → (CoalitionAgrees y x (InverseCoalition (Unwrap c)) v) 
             → result v x y
             → CoalitionAgrees w y (Unwrap c) v
             ------------------------------
             → result v w y
CorollaryTwo {n} {n>2} c v swf x y w ca-x>y in-ca-y>x swfx>y ca-w>y
  with x Fin.≟ w
... | true  because ofʸ  x≡w rewrite x≡w = swfx>y
... | false because ofⁿ ¬x≡w with y Fin.≟ w
... | false because ofⁿ ¬y≡w = 
  LemmaThree c v swf x y w ¬x≡w ¬y≡w ca-x>y in-ca-y>x swfx>y ca-w>y
... | true  because ofʸ  y≡w rewrite y≡w = ⊥-elim (Decisive-x>x v c w w refl ca-w>y)

LemmaFourSimilar : {m : ℕ}
                 → (c : Coalition m) 
                 → (v : Votes n n>2 m) 
                 → (a b x y : Fin n)
                 → ¬ (x ≡ a) 
                 → ¬ (y ≡ b)
                 → ¬ (x ≡ b) 
                 → ¬ (y ≡ a)
                 → (CoalitionAgrees x y c v)
                 → (CoalitionAgrees y x (InverseCoalition c) v)
                 → (CoalitionAgrees a b c v)
                 → Σ (Votes n n>2 m) 
                  λ v' → (Similar m a b (Zipped n>2 a b v v')
                        × Similar m x y (Zipped n>2 x y v' v)
                        ×  ElectionAgrees v' a x
                        ×  ElectionAgrees v' y b)
LemmaFourSimilar [] [] a b x y ¬x≡a ¬y≡b _ _ _ _ _ = [] , tt , tt , tt , tt
LemmaFourSimilar (false ∷ c) (p ∷ votes) a b x y ¬x≡a ¬y≡b ¬x≡b ¬y≡a
  (false-agrees c v₁ ca-x>y p) 
  (true-agrees .(InverseCoalition c) .v₁ inv-y>x .p yPx) 
  (false-agrees .c .v₁ ca-a>b .p) 
  with LemmaFourSimilar c votes a b x y ¬x≡a ¬y≡b ¬x≡b ¬y≡a ca-x>y inv-y>x ca-a>b 
... | votes' , sim-a-b , sim-x-y , ea-a-x , ea-y-b 
  with Alter-First p y
... | _ , p' , y-first , non-y-same
  with Alter-Last p' x
... | _ , p'' , x-last , non-x-same = p'' ∷ votes'
    , ((aPb-agree , bPa-agree) , sim-a-b) 
    , ((xPy-agree , yPx-agree) , sim-x-y) 
    , (x-last a (λ a≡x → ¬x≡a (Eq.sym a≡x)) , ea-a-x) 
    , (y>b , ea-y-b)
    where
      xPy-agree : P→Bool p'' x y ≡ P→Bool p x y
      xPy-agree with R-dec p y x | R-dec p'' y x
      ... | inj₁ _ | inj₁ _ = refl
      ... | inj₂ xPy | _ = ⊥-elim (yPx (P→R {v = p} xPy))
      ... | _ | inj₂ xP''y = ⊥-elim (xP''y (P→R {v = p''} (x-last y (P↛≡ {v = p} yPx))))
      
      yPx-agree : P→Bool p'' y x ≡ P→Bool p y x
      yPx-agree with R-dec p x y | R-dec p'' x y 
      ... | inj₁ xRy | _ = ⊥-elim (yPx xRy)  
      ... | _ | inj₁ xR''y = ⊥-elim (x-last y (P↛≡ {v = p} yPx) xR''y)   
      ... | inj₂ yPx | inj₂ yP''x = refl   

      aPb-agree : P→Bool p a b ≡ P→Bool p'' a b
      aPb-agree with non-x-same b a (λ b≡x → ¬x≡b (Eq.sym b≡x)) (λ a≡x → ¬x≡a (Eq.sym a≡x)) 
      ... | R''→R' , R'→R'' with non-y-same b a (λ b≡y → ¬y≡b (Eq.sym b≡y)) (λ a≡y → ¬y≡a (Eq.sym a≡y)) 
      ... | R→R' , R'→R with R-dec p b a | R-dec p'' b a
      ... | inj₁ _ | inj₁ _ = refl
      ... | inj₂ _ | inj₂ _ = refl
      ... | inj₁ bRa | inj₂ aP''b = ⊥-elim (aP''b (R''→R' (R→R' bRa)))
      ... | inj₂ aPb | inj₁ bR''a = ⊥-elim (aPb (R'→R (R'→R'' bR''a))) 

      bPa-agree : P→Bool p b a ≡ P→Bool p'' b a
      bPa-agree with non-x-same a b (λ a≡x → ¬x≡a (Eq.sym a≡x)) (λ b≡x → ¬x≡b (Eq.sym b≡x)) 
      ... | R''→R' , R'→R'' with non-y-same a b (λ a≡y → ¬y≡a (Eq.sym a≡y)) (λ b≡y → ¬y≡b (Eq.sym b≡y)) 
      ... | R→R' , R'→R with R-dec p a b | R-dec p'' a b 
      ... | inj₁ aRb | inj₁ aR''b = refl
      ... | inj₂ bPa | inj₂ bP''a = refl
      ... | inj₂ bPa | inj₁ aR''b = ⊥-elim (bPa (R'→R (R'→R'' aR''b)))
      ... | inj₁ aRb | inj₂ bP''a = ⊥-elim (bP''a (R''→R' (R→R' aRb)))

      y>b : P p'' y b
      y>b yR''b with b Fin.≟ x
      ... | true because ofʸ b≡x rewrite b≡x = x-last y ¬y≡b yR''b
      ... | false because ofⁿ ¬b≡x with non-x-same b y ¬b≡x (P↛≡ {v = p} yPx) 
      ... | R→R' , R'→R = y-first b (λ b≡y → ¬y≡b (Eq.sym b≡y)) (R'→R yR''b)
      
LemmaFourSimilar (true ∷ c) (p ∷ votes) a b x y ¬x≡a ¬y≡b ¬x≡b ¬y≡a
  (true-agrees c .votes ca-x>y .p xPy) 
  (false-agrees .(InverseCoalition c) .votes inv-y>x .p) 
  (true-agrees .c votes ca-a>b .p aPb) 
  with LemmaFourSimilar c votes a b x y ¬x≡a ¬y≡b ¬x≡b ¬y≡a ca-x>y inv-y>x ca-a>b 
... | votes' , sim-a-b , sim-x-y , ea-a-x , ea-y-b 
  with Alter-First p a 
... | _ , p' , a-first , non-a-same
  with Alter-Last p' b 
... | _ , p'' , b-last , non-b-same
    = (p'' ∷ votes') 
    , ((aPb-agree , bPa-agree) , sim-a-b) 
    , ((xPy-agree , yPx-agree) , sim-x-y) 
    , (a>x , ea-a-x) 
    , (b-last y ¬y≡b , ea-y-b)
    where
      aPb-agree : P→Bool p a b ≡ P→Bool p'' a b
      aPb-agree with R-dec p b a | R-dec p'' b a
      ... | inj₁ bRa | _ = ⊥-elim (aPb bRa)
      ... | _ | inj₁ bR''a = ⊥-elim (b-last a (P↛≡ {v = p} aPb) bR''a)
      ... | inj₂ _ | inj₂ _ = refl

      bPa-agree : P→Bool p b a ≡ P→Bool p'' b a
      bPa-agree with R-dec p a b | R-dec p'' a b 
      ... | inj₁ _ | inj₁ _ = refl
      ... | _ | inj₂ bP''a = 
        ⊥-elim (bP''a (P→R {v = p''} (b-last a (P↛≡ {v = p} aPb))))
      ... | inj₂ bPa | _ = 
        ⊥-elim (bPa (P→R {v = p} aPb))

      xPy-agree : P→Bool p'' x y ≡ P→Bool p x y
      xPy-agree with R-dec p y x | R-dec p'' y x
      ... | inj₁ yRx | _ = ⊥-elim (xPy yRx)
      ... | inj₂ xPy | inj₂ xP''y = refl
      ... | inj₂ xPy | inj₁ yR''x with non-b-same y x ¬y≡b ¬x≡b
      ... | R'→R'' , R''→R' with non-a-same y x ¬y≡a ¬x≡a
      ... | R→R' , R'→R = ⊥-elim (xPy (R'→R (R''→R' yR''x)))

      yPx-agree : P→Bool p'' y x ≡ P→Bool p y x
      yPx-agree with R-dec p x y | R-dec p'' x y
      ... | inj₁ _ | inj₁ _ = refl
      ... | inj₂ yPx | _ = ⊥-elim (xPy (P→R {v = p} yPx))
      ... | _ | inj₂ yP''x with non-b-same y x ¬y≡b ¬x≡b
      ... | R'→R'' , R''→R' with non-a-same y x ¬y≡a ¬x≡a
      ... | R→R' , R'→R = ⊥-elim (xPy (R'→R (R''→R' (P→R {v = p''} yP''x))))

      a>x : P p'' a x
      a>x xR''a with non-b-same x a ¬x≡b (P↛≡ {v = p} aPb)
      ... | R'→R'' , R''→R' = a-first x ¬x≡a (R''→R' xR''a)

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
... | true because ofʸ x≡a | _ rewrite x≡a = 
    CorollaryOne c v swf a y b ca-x>y inv-y>x res-x>y ca-a>b
... | _ | true because ofʸ y≡b rewrite y≡b = 
    CorollaryTwo c v swf x b a ca-x>y inv-y>x res-x>y ca-a>b 
... | false because ofⁿ ¬x≡a | false because ofⁿ ¬y≡b with y Fin.≟ a | x Fin.≟ b
... | true because ofʸ y≡a | false because ofⁿ ¬x≡b rewrite y≡a = {!   !}
LemmaFour c v x y swf ca-x>y inv-y>x res-x>y a b ca-a>b 
  | false because ofⁿ ¬x≡a | false because ofⁿ ¬y≡b
  | false because ofⁿ ¬y≡a | true because ofʸ x≡b rewrite x≡b 
  with CorollaryTwo c v swf b y a ca-x>y inv-y>x res-x>y {!   !} 
... | f = {!   !} 
  {-
  with CorollaryTwo c v swf b y a ca-x>y inv-y>x res-x>y
... | aPy with CorollaryOne c v swf b y a ca-x>y inv-y>x res-x>y
... | f = CorollaryOne c v swf a y b {!   !} {!   !} {!   !} {!   !}-}
LemmaFour c v x y swf ca-x>y inv-y>x res-x>y a b ca-a>b 
  | false because ofⁿ ¬x≡a | false because ofⁿ ¬y≡b
  | true because ofʸ y≡a | true because ofʸ x≡b rewrite x≡b | y≡a = {! contradcition  !}
LemmaFour c v x y swf ca-x>y inv-y>x res-x>y a b ca-a>b 
  | false because ofⁿ ¬x≡a | false because ofⁿ ¬y≡b 
  | false because ofⁿ ¬y≡a | false because ofⁿ ¬x≡b
  with LemmaFourSimilar (Unwrap c) v a b x y ¬x≡a ¬y≡b ¬x≡b ¬y≡a ca-x>y inv-y>x ca-a>b 
... | v' , sim-a-b , sim-x-y , ea-a-x , ea-y-b =
  BinaryIIA swf v v' a b sim-a-b
    (Transitive swf v' a x b 
      (Pareto swf v' a x ea-a-x)
      (Transitive swf v' x y b 
        (BinaryIIA swf v' v x y sim-x-y res-x>y)
        (Pareto swf v' y b ea-y-b)))

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