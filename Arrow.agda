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
    Result : {m : ℕ} → Votes n n>2 m → Fin n → Fin n → Set

-- the coalition of the whole is decisive

-- do william naming thingy

LemmaOne : (m : ℕ) 
         → (v : Votes n n>2 m)
         → (SWF Result)
         → Decisive (Whole m) v Result
LemmaOne m v swf a b ca = SWF.Pareto swf v a b (helper m v a b ca) where
  helper : (m : ℕ) 
         → (v : Votes n n>2 m) 
         → (a b : Fin n) 
         → CoalitionAgrees a b (Whole m) v 
         → ElectionAgrees v a b
  helper .0 [] a b c = tt
  helper (suc m) (x ∷ v) a b (true-agrees .(Whole m) .v c .x agrees) = agrees , (helper m v a b c)

LemmaTwoAlter : {_R_ : Fin n → Fin n → Set} 
              → (p : Preference n n>2 _R_)
              → (x y z : Fin n)
              → ¬ x ≡ z 
              → ¬ y ≡ z 
              → (P p y x) ⊎ (P p x z)
              → P p y z 
              ⊎ (Σ (Fin n → Fin n → Set) λ _R'_ 
                → Σ (Preference n n>2 _R'_) 
                  λ p' → (P→Bool p x z ≡ P→Bool p' x z 
                       ×  P→Bool p z x ≡ P→Bool p' z x)
                       × (P→Bool p' x y ≡ P→Bool p x y
                       ×  P→Bool p' y x ≡ P→Bool p y x)
                       × P p' y z)
LemmaTwoAlter {_R_ = _R_} p x y z ¬x≡z ¬y≡z (inj₁ yPx) 
  with R-dec p x z 
... | inj₁ xRz = inj₁ (λ zRy → yPx (R-trans p x z y xRz zRy))
... | inj₂ zPx with Alter-Z-Last p z 
... | _R'_ , p-z-last , z-last , not-z-same with Alter-Z-Last p-z-last x 
... | _R''_ , p-y>z>x , x-last , not-x-same = 
  inj₂ (_R''_
  , p-y>z>x 
  , (agree-x>z , agree-z>x) 
  , (agree-x>y , agree-y>x) 
  , yP''z) 
  where 
  
  ¬y≡x : ¬ y ≡ x 
  ¬y≡x = P↛≡ {v = p} yPx

  agree-z>x : true ≡ (P→Bool p-y>z>x z x)
  agree-z>x with R-dec p-y>z>x x z
  ... | inj₁ xR''z = ⊥-elim (x-last z (λ z≡x → ¬x≡z (Eq.sym z≡x)) xR''z)
  ... | inj₂ zP'x = refl

  agree-x>z : (P→Bool p x z) ≡ (P→Bool p-y>z>x x z)
  agree-x>z with R-dec p z x | R-dec p-y>z>x z x
  ... | inj₁ _ | inj₁ _ = refl
  ... | _ | inj₂ xP''z 
    = ⊥-elim (x-last z (λ z≡x → ¬x≡z (Eq.sym z≡x)) (P→R {v = p-y>z>x} xP''z))
  ... | inj₂ xPz | _ = ⊥-elim (xPz (P→R {v = p} zPx))

  agree-x>y : (P→Bool p-y>z>x x y) ≡ (P→Bool p x y)
  agree-x>y with R-dec p y x | R-dec p-y>z>x y x
  ... | inj₁ _ | inj₁ _ = refl
  ... | inj₁ yRx | inj₂ xP''y 
    = ⊥-elim (x-last y ¬y≡x (P→R {v = p-y>z>x} xP''y))
  ... | inj₂ xPy | _ = ⊥-elim (xPy (P→R {v = p} yPx))

  agree-y>x : (P→Bool p-y>z>x y x) ≡ (P→Bool p y x)
  agree-y>x with R-dec p x y | R-dec p-y>z>x x y
  ... | inj₁ xRy | _ = ⊥-elim (yPx xRy)
  ... | _ | inj₁ xR''y = ⊥-elim (x-last y ¬y≡x xR''y)
  ... | inj₂ _ | inj₂ _ = refl

  yP''z : z R'' y → ⊥
  yP''z zR''y with not-x-same z y (λ z≡x → ¬x≡z (Eq.sym z≡x)) ¬y≡x
  ... | _ , R''→R' = z-last y ¬y≡z (R''→R' zR''y)
  
LemmaTwoAlter {_R_ = _R_} p x y z  ¬x≡z ¬y≡z (inj₂ xPz)
  with R-dec p y x 
... | inj₁ yRx = inj₁ (λ zRy → xPz (R-trans p z y x zRy yRx))
... | inj₂ xPy with Alter-Z-Last p z 
... | _R'_ , p-z-last , z-last , not-z-same 
  = inj₂ (_R'_ , p-z-last 
  , (agree-x>z , agree-z>x) 
  , (agree-x>y , agree-y>x) 
  , z-last y ¬y≡z) 
  where
    agree-x>z : P→Bool p x z ≡ P→Bool p-z-last x z
    agree-x>z with R-dec p z x | R-dec p-z-last z x 
    ... | inj₁ zRx | _ = ⊥-elim (xPz zRx)
    ... | _ | inj₁ zR'x = ⊥-elim (z-last x ¬x≡z zR'x)
    ... | inj₂ _ | inj₂ _ = refl

    agree-z>x : P→Bool p z x ≡ P→Bool p-z-last z x
    agree-z>x with R-dec p x z | R-dec p-z-last x z 
    ... | inj₁ _ | inj₁ _ = refl
    ... | _ | inj₂ zP'x = ⊥-elim (z-last x ¬x≡z (P→R {v = p-z-last} zP'x))
    ... | inj₂ zPx | inj₁ xRz = ⊥-elim (xPz (P→R {v = p} zPx))

    agree-x>y : P→Bool p-z-last x y ≡ true
    agree-x>y with R-dec p-z-last y x
    ... | inj₂ _ = refl
    ... | inj₁ yR'x with not-z-same y x ¬y≡z ¬x≡z
    ... | _ , R'→R = ⊥-elim (xPy (R'→R yR'x))

    agree-y>x : P→Bool p-z-last y x ≡ P→Bool p y x
    agree-y>x with R-dec p-z-last x y | R-dec p x y 
    ... | inj₁ _ | inj₁ _ = refl
    ... | _ | inj₂ yPx = ⊥-elim (yPx (P→R {v = p} xPy))
    ... | inj₂ yP'x | inj₁ xRy with not-z-same x y ¬x≡z ¬y≡z 
    ... | R→R' , R'→R = ⊥-elim (yP'x (R→R' xRy))

LemmaTwoSimilar : (m : ℕ) 
                → (c : Coalition m) 
                → (v : Votes n n>2 m) 
                → (x y z : Fin n) 
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z) 
                → (CoalitionAgrees y x (InverseCoalition c) v)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n n>2 m) λ v' 
                                    → (Similar m x z (Zipped n>2 x z v v')  
                                    × Similar m x y (Zipped n>2 x y v' v)
                                    × ElectionAgrees v' y z)
LemmaTwoSimilar zero [] [] x y z ¬x≡z ¬y≡z _ _ = [] , (tt , (tt , tt))
LemmaTwoSimilar (suc m) (false ∷ c) (p ∷ v) x y z ¬x≡z ¬y≡z 
  (true-agrees .(InverseCoalition c) .v inv-y>x .p yPx) 
  (false-agrees .c .v ca-x>z .p) 
  with LemmaTwoSimilar m c v x y z ¬x≡z ¬y≡z inv-y>x ca-x>z
... | alt-v , sim-x-z , sim-x-y , alt-y>z 
  with LemmaTwoAlter p x y z ¬x≡z ¬y≡z (inj₁ yPx) 
... | inj₁ yPz = (p ∷ alt-v) 
    , ((refl , refl) , sim-x-z) 
    , ((refl , refl) , sim-x-y) 
    , yPz , alt-y>z
... | inj₂ (_ , p' , p'-x-z , p'-x-y , yP'z) = (p' ∷ alt-v) 
    , (p'-x-z , sim-x-z) 
    , (p'-x-y , sim-x-y)
    , yP'z , alt-y>z
LemmaTwoSimilar (suc m) (true ∷ c) (p ∷ v) x y z ¬x≡z ¬y≡z 
  (false-agrees .(InverseCoalition c) .v inv-y>x .p) 
  (true-agrees .c .v ca-x>z .p xPz) 
  with LemmaTwoSimilar m c v x y z ¬x≡z ¬y≡z inv-y>x ca-x>z
... | alt-v , sim-x-z , sim-x-y , alt-y>z 
  with LemmaTwoAlter p x y z ¬x≡z ¬y≡z (inj₂ xPz) 
... | inj₁ yPz = (p ∷ alt-v) 
    , ((refl , refl) , sim-x-z) 
    , ((refl , refl) , sim-x-y) 
    , yPz , alt-y>z
... | inj₂ (_ , p' , p'-x-z , p'-x-y , yP'z) = (p' ∷ alt-v) 
    , (p'-x-z , sim-x-z) 
    , (p'-x-y , sim-x-y)
    , yP'z , alt-y>z

LemmaTwo : (m : ℕ) 
         → (c : Coalition m) 
         → (v : Votes n n>2 m) 
         → SWF Result
         → (x y z : Fin n) 
         → ¬ (x ≡ z) 
         → ¬ (y ≡ z) 
         → (CoalitionAgrees y x (InverseCoalition c) v)
         → Result v x y
         → (CoalitionAgrees x z c v)
         ------------------------------
         → Result v x z
LemmaTwo m c v swf x y z ¬x≡z ¬y≡z in-ca-y>x swfx>y ca-x>z 
  with LemmaTwoSimilar m c v x y z ¬x≡z ¬y≡z in-ca-y>x ca-x>z                                                       
... | v' , v'-sim-xz , v-sim-xy , v'-y>z = 
  SWF.BinaryIIA swf v v' x z v'-sim-xz 
    (SWF.Transitive swf v' x y z (SWF.BinaryIIA swf v' v x y v-sim-xy swfx>y) 
      (SWF.Pareto swf v' y z v'-y>z))

StrictlyDecisive-x>x : (m : ℕ)
             → (c : NonEmptyCoalition m)
             → (v : Votes n n>2 m) 
             → (a b : Fin n)
             → (a ≡ b)
             → StrictlyDecisive-a>b (Unwrap c) v Result a b 
StrictlyDecisive-x>x m c v a b a≡b = λ ca → ⊥-elim (helper v c a b a≡b ca)
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

CorollaryOne : (m : ℕ) 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n n>2 m)
             → SWF Result
             → (x y w : Fin n) 
             → (CoalitionAgrees y x (InverseCoalition (Unwrap c)) v)
             → Result v x y
             → (CoalitionAgrees x w (Unwrap c) v)
             → Result v x w
CorollaryOne {n} {n>2} {Result = Result} m c v swf x y w in-ca-y>x swfx>y 
  with x Fin.≟ w
... | true because ofʸ x≡w = 
  StrictlyDecisive-x>x {Result = Result} m c v x w x≡w 
... | false because ofⁿ ¬x≡w with y Fin.≟ w
... | false because ofⁿ ¬y≡w = 
  LemmaTwo {Result = Result} m (Unwrap c) v swf x y w ¬x≡w ¬y≡w in-ca-y>x swfx>y
... | true because ofʸ y≡w rewrite y≡w = λ _ → swfx>y

LemmaThreeAlter : {_R_ : Fin n → Fin n → Set} 
              → (p : Preference n n>2 _R_)
              → (x y z : Fin n) 
              → (P p y x) ⊎ (P p z y)
              → ¬ (x ≡ z) 
              → ¬ (y ≡ z)
              → P p z x 
              ⊎ (Σ (Fin n → Fin n → Set) λ _R'_ 
                → Σ (Preference n n>2 _R'_) 
                  λ p' → (P→Bool p z y ≡ P→Bool p' z y 
                       ×  P→Bool p y z ≡ P→Bool p' y z)
                       × (P→Bool p' x y ≡ P→Bool p x y
                       ×  P→Bool p' y x ≡ P→Bool p y x)
                       × P p' z x) 
LemmaThreeAlter {_R_ = _R_} p x y z (inj₁ yPx) ¬x≡z ¬y≡z with R-dec p z y 
... | inj₁ zRy = inj₁ (λ xRz → yPx (R-trans p x z y xRz zRy))
... | inj₂ yPz with Alter-Z-Last p x 
... | _R'_ , p' , x-last , same-non-x 
  = inj₂ (_R'_ , p' 
  , {!   !} 
  , {!   !} 
  , x-last z (λ z≡x → ¬x≡z (Eq.sym z≡x)))
LemmaThreeAlter {_R_ = _R_} p x y z (inj₂ zPy) ¬x≡z ¬y≡z with R-dec p x y 
... | f = {!   !} 

LemmaThreeSimilar : (m : ℕ) 
                  → (c : Coalition m) 
                  → (v : Votes n n>2 m) 
                  → (x y z : Fin n) 
                  → ¬ (x ≡ z) 
                  → ¬ (y ≡ z)
                  → (CoalitionAgrees y x (InverseCoalition c) v)
                  → (CoalitionAgrees z y c v)
                  → Σ (Votes n n>2 m) λ v' 
                    → (Similar m z y (Zipped n>2 z y v v')  
                    ×  Similar m x y (Zipped n>2 x y v' v)
                    ×  ElectionAgrees v' z x)
LemmaThreeSimilar zero [] [] x y z ¬x≡z ¬y≡z _ _ = [] , (tt , (tt , tt))
LemmaThreeSimilar (suc m) (false ∷ c) (p ∷ rem) x y z ¬x≡z ¬y≡z 
  (true-agrees .(InverseCoalition c) .rem inv-y>x .p yPx) 
  (false-agrees .c .rem ca-z>y .p) 
  with LemmaThreeSimilar m c rem x y z ¬x≡z ¬y≡z inv-y>x ca-z>y
... | altered-votes , alt-sim-z-y , alt-sim-x-y , alt-z>x 
  with LemmaThreeAlter p x y z (inj₁ yPx) ¬x≡z ¬y≡z 
... | inj₁ zPx = (p ∷ altered-votes) 
    , ((refl , refl) , alt-sim-z-y) 
    , ((refl , refl) , alt-sim-x-y) 
    , (zPx , alt-z>x)
... | inj₂ (_R'_ , p' , p-sim-z-y , p-sim-x-y , p'-z>x) = 
      (p' ∷ altered-votes) 
    , (p-sim-z-y , alt-sim-z-y) 
    , (p-sim-x-y , alt-sim-x-y) 
    , (p'-z>x , alt-z>x)
LemmaThreeSimilar (suc m) (true ∷ c) (p ∷ rem) x y z ¬x≡z ¬y≡z 
  (false-agrees .(InverseCoalition c) .rem inv-y>x .p) 
  (true-agrees .c .rem ca-z>y .p zPy) with LemmaThreeSimilar m c rem x y z ¬x≡z ¬y≡z inv-y>x ca-z>y
... | altered-votes , alt-sim-z-y , alt-sim-x-y , alt-z>x 
  with LemmaThreeAlter p x y z (inj₂ zPy) ¬x≡z ¬y≡z 
... | inj₁ zPx = (p ∷ altered-votes) 
    , ((refl , refl) , alt-sim-z-y) 
    , ((refl , refl) , alt-sim-x-y) 
    , (zPx , alt-z>x)
... | inj₂ (_R'_ , p' , p-sim-z-y , p-sim-x-y , p'-z>x) = 
      (p' ∷ altered-votes) 
    , (p-sim-z-y , alt-sim-z-y) 
    , (p-sim-x-y , alt-sim-x-y) 
    , (p'-z>x , alt-z>x)

LemmaThree : (m : ℕ) 
           → (c : Coalition m) 
           → (v : Votes n n>2 m) 
           → SWF Result
           → (x y z : Fin n) 
           → ¬ (x ≡ z) 
           → ¬ (y ≡ z) 
           → (CoalitionAgrees y x (InverseCoalition c) v)
           → Result v x y
           → (CoalitionAgrees z y c v)
           → Result v z y
LemmaThree m c v swf x y z ¬x≡z ¬y≡z in-ca-y>x swfx>y ca-z>y
  with LemmaThreeSimilar m c v x y z ¬x≡z ¬y≡z in-ca-y>x ca-z>y
... | v' , v'-sim-zy , v'-sim-xy , v'-z>x = 
  SWF.BinaryIIA swf v v' z y v'-sim-zy 
    (SWF.Transitive swf v' z x y (SWF.Pareto swf v' z x v'-z>x) 
      (SWF.BinaryIIA swf v' v x y v'-sim-xy swfx>y))

CorollaryTwo : (m : ℕ) 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n n>2 m) 
             → SWF Result
             → (x y w : Fin n) 
             → (CoalitionAgrees y x (InverseCoalition (Unwrap c)) v)
             → Result v x y 
             → StrictlyDecisive-a>b (Unwrap c) v Result w y
CorollaryTwo {n} {n>2} {Result = Result} m c v swf x y w 
  in-ca-y>x swfx>y with y Fin.≟ w 
... | true because ofʸ y≡w = 
  StrictlyDecisive-x>x {Result = Result} m c v w y (Eq.sym y≡w) 
... | false because ofⁿ ¬y≡w with x Fin.≟ w
... | false because ofⁿ ¬x≡w = 
  LemmaThree {Result = Result} m (Unwrap c) v swf x y w ¬x≡w ¬y≡w in-ca-y>x swfx>y
... | true because ofʸ y≡w rewrite y≡w = λ _ → swfx>y
{-
LemmaFourAlter : {_R_ : Fin n → Fin n → Set} 
               → (p : Preference n n>2 _R_)
               → (x y v w : Fin n)  
               → ¬ (x ≡ v) 
               → ¬ (y ≡ w)
               → Σ (Fin n → Fin n → Set) 
                λ _R'_ → Σ (Preference n n>2 _R'_) 
                  λ P' → P→Bool p v w ≡ P→Bool P' v w
                  × P P' v x
                  × Σ (Fin n → Fin n → Set) 
                    λ _R''_ → Σ (Preference n n>2 _R''_) 
                      λ P'' → (P→Bool P' x w ≡ P→Bool P'' x w
                      × P→Bool P'' x y ≡ P→Bool p x y
                      × P P'' y w)
LemmaFourAlter {_R_ = _R_} p x y v w ¬x≡v ¬y≡w 
  with R-dec p x v | R-dec p w y 
LemmaFourAlter {_R_ = _R_} p x y v w ¬x≡v ¬y≡w | inj₁ xRv | inj₁ wRy = {!   !}
LemmaFourAlter {_R_ = _R_} p x y v w ¬x≡v ¬y≡w | inj₁ xRv | inj₂ yPw = 
  {!   !} , {!   !} , {!   !} , {!   !} , _R_ , p , {!   !} , refl , yPw
LemmaFourAlter {n = n} {n>2 = n>2} {_R_ = _R_} 
  p x y v w ¬x≡v ¬y≡w | inj₂ vPx | inj₁ wRy 
  with R-dec p x w | R-dec p x y
... | inj₂ wPx | inj₂ yPx =
   _R_ , p , refl , vPx , _R'_ , P' , {!   !} , {!   !}
       , λ {(y-first .y) → ¬y≡w refl
          ; (orig .w .y ¬y≡y _) → ¬y≡y refl}
   where
    data _R'_ : Fin n → Fin n → Set where
      y-first : ∀ a → y R' a
      orig    : ∀ a b
              → ¬ (b ≡ y)
              → a R  b
              → a R' b
    
    R'-trans : (a b c : Fin n) → a R' b → b R' c → a R' c
    R'-trans a b c (y-first .a) (y-first .c) = y-first c
    R'-trans a b c (y-first .b) (orig .b .c ¬c≡y bRc) = y-first c
    R'-trans a b c (orig .a .b ¬b≡b _) (y-first .c) = ⊥-elim (¬b≡b refl)
    R'-trans a b c (orig .a .b ¬b≡y aRb) (orig .b .c ¬c≡y bRc) = 
      orig a c ¬c≡y (R-trans p a b c aRb bRc)

    R'-complete : (a b : Fin n) → (a R' b) ⊎ (b R' a)
    R'-complete a b  with a Fin.≟ y | b Fin.≟ y 
    ... | true because  ofʸ  a≡y | _ rewrite Eq.sym a≡y = inj₁ (y-first b)
    ... | _ | true because ofʸ b≡y rewrite Eq.sym b≡y = inj₂ (y-first a)
    ... | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡y 
      with R-complete p a b 
    ... | inj₁ aRb = inj₁ (orig a b ¬b≡y aRb)
    ... | inj₂ bRa = inj₂ (orig b a ¬a≡y bRa)

    R'-dec : (a b : Fin n) → (a R' b) ⊎ ¬ (a R' b)
    R'-dec a b with a Fin.≟ y 
    ... | true because ofʸ   a≡y rewrite Eq.sym a≡y = inj₁ (y-first b)
    ... | false because ofⁿ ¬a≡y with b Fin.≟ y 
    ... | true because ofʸ   b≡y = 
      inj₂ (λ {(y-first .b) → ¬a≡y refl
            ; (orig .a .b ¬b≡y _) → ¬b≡y b≡y})
    ... | false because ofⁿ ¬b≡y with R-dec p a b 
    ... | inj₁ aRb = inj₁ (orig a b ¬b≡y aRb)
    ... | inj₂ bPa = 
      inj₂ (λ {(y-first .b) → ¬a≡y refl
            ; (orig .a .b _ aRb) → bPa aRb})

    P' : Preference n n>2 _R'_
    P' = record { R-trans = R'-trans 
       ; R-complete = R'-complete 
       ; R-dec = R'-dec }
    {-
    agrees-x-w : (P→Bool p x w) ≡ (P→Bool P' x w)
    agrees-x-w with R-dec p x w | R-dec P' x w
    ... | inj₁ xRw | _ = ⊥-elim (wPx xRw)
    ... | inj₂ wPx | inj₁ (y-first x) = ⊥-elim (yPx (R-refl p y y refl))
    ... | inj₂ wPx | inj₁ (orig .x .w _ xRw) = ⊥-elim (wPx xRw)
    ... | inj₂ wPx | inj₂ wP'x = refl 

    agrees-x-y : (P→Bool P' x y) ≡ false
    agrees-x-y with R-dec P' x y
    ... | inj₁ (y-first .x) = ⊥-elim (yPx (R-refl p y y refl))
    ... | inj₁ (orig .x .y ¬y≡y _) = ⊥-elim (¬y≡y refl)
    ... | inj₂ _ = refl-}

... | inj₁ xRw | f = 
  _R_ , p , refl , vPx , {!   !} , {!   !} , {!   !} , {!   !} , {!   !}
... | inj₂ wPx | inj₁ xRy with R-dec p v w 
... | inj₁ vRw = {!   !} {- R'' x > y | y > w
  _R'_ , P' , agrees-v-w 
  , (λ {(v-first .v _) → ¬x≡v refl
      ; (orig .x .v _ ¬v≡v _) → ¬v≡v refl
      ; (w-last .x ¬v≡w) → ¬v≡w refl}) 
  , _R'_ , P' , refl , agrees-x-y 
  , λ {(v-first .y ¬v≡w) → ¬v≡w refl
     ; (orig .w .y ¬w≡w _ _) → ¬w≡w refl
     ; (w-last .w _) → ¬y≡w refl}
  where
    data _R'_ : Fin n → Fin n → Set where
      v-first : ∀ a 
              → ¬ (v ≡ w) 
              → v R' a

      orig    : ∀ a b
              → ¬ (a ≡ w)
              → ¬ (b ≡ v)
              → a R  b
              → a R' b

      w-last : ∀ a 
             → ¬ (v ≡ w) 
             → a R' w
    
    R'-trans : (a b c : Fin n) → a R' b → b R' c → a R' c
    R'-trans a b c (v-first .a ¬v≡w) (v-first .c _) = v-first c ¬v≡w
    R'-trans a b c (v-first .b ¬v≡w) (orig .b .c ¬b≡w ¬c≡v bRc) = v-first c ¬v≡w
    R'-trans a b c (orig .a .b ¬a≡w ¬b≡b _) (v-first .c _) = ⊥-elim (¬b≡b refl)
    R'-trans a b c (orig .a .b ¬a≡w ¬b≡v aRb) (orig .b .c ¬b≡w ¬c≡v bRc) = 
      orig a c ¬a≡w ¬c≡v (R-trans p a b c aRb bRc)
    R'-trans a b c (v-first .b ¬v≡w) (w-last .b ¬a≡c) = v-first c ¬v≡w
    R'-trans a b c (orig .a .b ¬a≡w ¬b≡v aRb) (w-last .b ¬a≡c) = w-last a ¬a≡c
    R'-trans a b c (w-last .a ¬b≡b) (v-first .c _) = ⊥-elim (¬b≡b refl)
    R'-trans a b c (w-last .a ¬v≡b) (orig .b .c ¬b≡b _ _) = ⊥-elim (¬b≡b refl)
    R'-trans a b c (w-last .a ¬v≡b) (w-last .b _) = w-last a ¬v≡b

    R'-complete : (a b : Fin n) → (a R' b) ⊎ (b R' a)
    R'-complete a b with a Fin.≟ v | b Fin.≟ v 
    ... | true because  ofʸ  a≡v | _ rewrite Eq.sym a≡v = inj₁ (v-first b {!   !})
    ... | _ | true because ofʸ b≡v rewrite Eq.sym b≡v = inj₂ (v-first a {!   !})
    ... | false because ofⁿ ¬a≡v | false because ofⁿ ¬b≡v 
      with a Fin.≟ w | b Fin.≟ w 
    ... | true because ofʸ a≡w | _ rewrite Eq.sym a≡w = 
      inj₂ (w-last b (λ v≡a → ¬a≡v (Eq.sym v≡a)))
    ... | false because ofⁿ ¬a≡w | true because ofʸ b≡w 
      rewrite Eq.sym b≡w = inj₁ (w-last a (λ v≡b → ¬b≡v (Eq.sym v≡b)))
    ... | false because ofⁿ ¬a≡w | false because ofⁿ ¬b≡w 
      with R-complete p a b 
    ... | inj₁ aRb = inj₁ (orig a b ¬a≡w ¬b≡v aRb)
    ... | inj₂ bRa = inj₂ (orig b a ¬b≡w ¬a≡v bRa)

    R'-dec : (a b : Fin n) → (a R' b) ⊎ ¬ (a R' b)
    R'-dec a b with a Fin.≟ v 
    ... | true  because ofʸ  a≡v rewrite Eq.sym a≡v = inj₁ (v-first b {!   !})
    ... | false because ofⁿ ¬a≡v with a Fin.≟ w | b Fin.≟ w | b Fin.≟ v 
    ... | true because ofʸ a≡w | false because ofⁿ ¬b≡w | _ rewrite a≡w
      = inj₂ (λ {(v-first .b _) → ¬a≡v refl
               ; (orig .w .b ¬w≡w _ _) → ¬w≡w refl
               ; (w-last .w ¬v≡b) → ¬b≡w refl})
    ... | true because ofʸ a≡w | true  because ofʸ  b≡w | _
      rewrite a≡w | b≡w = inj₁ (w-last w (λ v≡w → ¬a≡v (Eq.sym v≡w)))
    ... | false because ofⁿ ¬a≡w | false because ofⁿ ¬b≡w | true  because ofʸ  b≡v 
      = inj₂ (λ {(v-first .b _) → ¬a≡v refl
               ; (orig .a .b _ ¬b≡v _) → ¬b≡v b≡v
               ; (w-last .a ¬v≡b) → ¬v≡b (Eq.sym b≡v)})
    ... | false because ofⁿ ¬a≡w | true because ofʸ b≡w | false because ofⁿ ¬b≡v 
      rewrite b≡w = inj₁ (w-last a (λ v≡w → ¬b≡v (Eq.sym v≡w)))
    ... | false because ofⁿ ¬a≡w | true because ofʸ b≡w | true  because ofʸ  b≡v 
      = inj₂ λ {(v-first .b _) → ¬a≡v refl
              ; (orig .a .b _ ¬b≡v _) → ¬b≡v b≡v
              ; (w-last .a ¬v≡b) → ¬v≡b (Eq.sym b≡v)}
    ... | false because ofⁿ ¬a≡w | false because ofⁿ ¬b≡w | false because ofⁿ ¬b≡v with R-dec p a b 
    ... | inj₁ aRb = inj₁ (orig a b ¬a≡w ¬b≡v aRb)
    ... | inj₂ aPb = inj₂ (λ {(v-first .b _) → ¬a≡v refl
                            ; (orig .a .b _ _ aRb) → aPb aRb
                            ; (w-last .a _) → ¬b≡w refl})

    P' : Preference n n>2 _R'_
    P' = record { R-trans = R'-trans 
       ; R-complete = R'-complete 
       ; R-dec = R'-dec }

    agrees-v-w : true ≡ P→Bool P' v w
    agrees-v-w = ?

    agrees-x-y : P→Bool P' x y ≡ true
    agrees-x-y = ?
    -}
... | inj₂ wPv = 
  {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !}

LemmaFourAlter {_R_ = _R_} p x y v w ¬x≡v ¬y≡w | inj₂ vPx | inj₂ yPw = 
  _R_ , p , refl , vPx , _R_ , p , refl , refl , yPw

LemmaFourSimilar : (m : ℕ) 
                → (c : Coalition m) 
                → (ballots : Votes n n>2 m) 
                → (x y v w : Fin n) 
                → ¬ (x ≡ v) 
                → ¬ (y ≡ w)
                → (CoalitionAgrees x y c ballots)
                → Σ (Votes n n>2 m) λ ballots'
                  → (Similar m v w (Zipped n>2 v w ballots ballots')
                  × ElectionAgrees ballots' v x
                  × Σ (Votes n n>2 m) λ ballots''
                    → (Similar m x w (Zipped n>2 x w ballots' ballots''))
                    × (Similar m x y (Zipped n>2 x y ballots'' ballots)
                    × ElectionAgrees ballots'' y w))
LemmaFourSimilar m c [] x y v w _ _ _ = [] , tt , tt , [] , tt , tt , tt 
LemmaFourSimilar (suc m') (false ∷ c) (p ∷ ballots) x y v w ¬x≡v ¬y≡w
  (false-agrees .c .ballots ca-x>y .p)
  with LemmaFourSimilar m' c ballots x y v w ¬x≡v ¬y≡w ca-x>y
... | b' , sim-b'-v-w , b'-v>x , b'' , sim-b-'-b''-x-w , sim-b-''-b-x-y , b''-y>w
  with LemmaFourAlter p x y v w ¬x≡v ¬y≡w
... | _ , P' , sim-v-w , P'vx , _ , P'' , sim-x-w , sim-x-y , P''yw
    = (P' ∷ b') 
    , (sim-v-w , sim-b'-v-w) 
    , ((P'vx , b'-v>x) 
    , ((P'' ∷ b'') 
      , ((sim-x-w , sim-b-'-b''-x-w) 
      , ((sim-x-y , sim-b-''-b-x-y) 
      ,  (P''yw , b''-y>w))))) 
LemmaFourSimilar (suc m') (true ∷ c) (p ∷ ballots) x y v w ¬x≡v ¬y≡w
  (true-agrees .c .ballots ca-x>y .p xPy)
  with LemmaFourSimilar m' c ballots x y v w ¬x≡v ¬y≡w ca-x>y
... | b' , sim-b'-v-w , b'-v>x , b'' , sim-b-'-b''-x-w , sim-b-''-b-x-y , b''-y>w 
    with LemmaFourAlter p x y v w ¬x≡v ¬y≡w
... | _ , P' , sim-v-w , P'vx , _ , P'' , sim-x-w , sim-x-y , P''yw
    = (P' ∷ b') 
    , (sim-v-w , sim-b'-v-w) 
    , ((P'vx , b'-v>x) 
    , ((P'' ∷ b'') 
      , ((sim-x-w , sim-b-'-b''-x-w) 
      , ((sim-x-y , sim-b-''-b-x-y) 
      ,  (P''yw , b''-y>w))))) 
-}
LemmaFour : (m : ℕ)
          → (c : SingletonCoalition m)
          → (ballots : Votes n n>2 m)
          → SWF Result
          → (v w : Fin n)
          → CoalitionAgrees v w (c .proj₁) ballots
          → Result ballots v w
LemmaFour m (c , mc) ballots swf v w ca-v>w = ? {-
  with x Fin.≟ v | y Fin.≟ w
... | true because ofʸ x≡v | false because ofⁿ ¬y≡w rewrite x≡v = 
  CorollaryOne m {!   !} ballots swf v y w {!   !} ca-v>w
... | false because ofⁿ ¬x≡v | true because ofʸ y≡w rewrite y≡w = 
  CorollaryTwo m {!   !} ballots swf x w v {!   !} ca-v>w
... | true  because ofʸ x≡v | true  because ofʸ y≡w rewrite x≡v | y≡w = swf-x>y 
... | false because ofⁿ ¬x≡v | false because ofⁿ ¬y≡w = ?
  with LemmaFourSimilar m c ballots x y v w ¬x≡v ¬y≡w ca-x>y 
... | b' , sim-b'-v-w , b'-v>x , b'' , sim-b-'-b''-x-w , sim-b-''-b-x-y , b''-y>w = 
    SWF.BinaryIIA swf ballots b' v w sim-b'-v-w 
      (SWF.Transitive swf b' v x w (SWF.Pareto swf b' v x b'-v>x) 
        (SWF.BinaryIIA swf b' b'' x w sim-b-'-b''-x-w 
          (SWF.Transitive swf b'' x y w 
            (SWF.BinaryIIA swf b'' ballots x y sim-b-''-b-x-y swf-x>y) 
            (SWF.Pareto swf b'' y w b''-y>w)))) -}
{-
LemmaFive : {m : ℕ}
         → (ballots : Votes n n>2 m)
         → SWF Result
         → Σ (SingletonCoalition m) λ c → 
          (Σ (Fin n) λ x → Σ (Fin n) λ y → 
            Result ballots x y × CoalitionAgrees x y (c .proj₁) ballots)
LemmaFive ballots swf = {!   !}



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