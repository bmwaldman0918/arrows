module Arrow where

open import Voter
open WeakPreference
open Preference
open StrictPreference
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
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
  variable
    n : ℕ
    n>2 : n ℕ.> 2

-- the coalition of the whole is decisive

LemmaOne : (m : ℕ) → (v : Votes n n>2 m) → Decisive (Whole m) v
LemmaOne m v a b ca = Pareto a b (helper m v a b ca) where
  helper : (m : ℕ) → (v : Votes n n>2 m) → (a b : Fin n) → CoalitionAgrees a b (Whole m) v → ElectionAgrees v a b
  helper .0 [] a b c = tt
  helper (suc m) (x ∷ v) a b (true-agrees .(Whole m) .v c .x agrees) = agrees , (helper m v a b c)

LemmaTwoAlter : {_R_ : Fin n → Fin n → Set} 
              → (head : Preference n n>2 _R_)
              → (x y z : Fin n) 
              → (P head y x) ⊎ (P head x z)
              → ¬ (x ≡ z) 
              → ¬ (y ≡ z)
              → Σ (Fin n → Fin n → Set) λ _R'_ → Σ (Preference n n>2 _R'_) λ P' → R→Bool head x z ≡ R→Bool P' x z × R→Bool P' x y ≡ R→Bool head x y × P P' y z
LemmaTwoAlter {_R_ = _R_} head x y z yPx⊎xPz ¬x≡z ¬y≡z with R-dec head z y
... | inj₁ zRy = R' head y z ¬y≡z zRy , P' head y z zRy ¬y≡z 
                                      , agrees-x-z head x y z yPx⊎xPz ¬x≡z ¬y≡z zRy 
                                      , agrees-x-y head x y z ¬x≡z ¬y≡z zRy 
                                      , λ {(zRx∧yRx→zR'x .z .y _ yPy zRy) → P↛≡ {v = head} yPy Eq.refl
                                        ; (original .z .y ¬z≡z zRy) → ¬z≡z Eq.refl
                                        ; (y>z .z .y ¬z≡z _ _) → ¬z≡z Eq.refl 
                                        ; (zRz .z .y _ y≡z) → ¬y≡z y≡z
                                        ; (yRz .z .y _ y≡z) → ¬y≡z y≡z}
  where
    data R' {_R_ : Fin n → Fin n → Set} 
            (head : Preference n n>2 _R_) 
            (y z : Fin n)
            (¬y≡z : ¬ y ≡ z) 
            (zRy : z R y) : Fin n → Fin n → Set where

        zRx∧yRx→zR'x : (a b : Fin n) 
                     → (a ≡ z)
                     → P head y b
                     → z R b
                     → R' head y z ¬y≡z zRy a b

        original     : (a b : Fin n) 
                     → ¬ (a ≡ z)
                     → a R b 
                     → R' head y z ¬y≡z zRy a b

        y>z         : (a b : Fin n)
                     → ¬ (a ≡ z)
                     → (a R y)
                     → (P head z b)
                     → R' head y z ¬y≡z zRy a b

        zRz          : (a b : Fin n) 
                     → (a R z)
                     → (b ≡ z)
                     → R' head y z ¬y≡z zRy a b
                     
        yRz          : (a b : Fin n) 
                     → (a R y)
                     → (b ≡ z)
                     → R' head y z ¬y≡z zRy a b

    R'-trans : {_R_ : Fin n → Fin n → Set} 
           → (head : Preference n n>2 _R_)
           → (y z : Fin n)
           → (zRy : z R y)
           → (¬y≡z : ¬ y ≡ z)
           → (a b c : Fin n)
           → R' head y z ¬y≡z zRy a b 
           → R' head y z ¬y≡z zRy b c 
           → R' head y z ¬y≡z zRy a c
    R'-trans head y z zRy ¬y≡z a b c (zRx∧yRx→zR'x .a .b a≡z yPb zRb) (zRx∧yRx→zR'x .b .c b≡z yPc zRc) = zRx∧yRx→zR'x a c a≡z yPc zRc
    R'-trans head y z zRy ¬y≡z a b c (zRx∧yRx→zR'x .a .b a≡z yPb zRb) (original .b .c ¬b≡z bRc) = zRx∧yRx→zR'x a c a≡z (λ cRy → yPb (R-trans head b c y bRc cRy)) (R-trans head z b c zRb bRc)
    R'-trans head y z zRy ¬y≡z a b c (zRx∧yRx→zR'x .a .b a≡z yPb zRb) (y>z .b .c ¬b≡z bRy zPc) = ⊥-elim (yPb bRy)
    R'-trans head y z zRy ¬y≡z a b c (zRx∧yRx→zR'x .a .b a≡z yPb zRb) (zRz .b .c bRz c≡z) = zRz a c (R-refl head a z a≡z) c≡z
    R'-trans head y z zRy ¬y≡z a b c (zRx∧yRx→zR'x .a .b a≡z yPb zRb) (yRz .b .c bRy c≡z) = zRz a c (R-refl head a z a≡z) c≡z
    R'-trans head y z zRy ¬y≡z a b c (original .a .b ¬a≡z aRb) (zRx∧yRx→zR'x .b .c b≡z yPc zRc) rewrite b≡z = original a c ¬a≡z (R-trans head a z c aRb zRc)
    R'-trans head y z zRy ¬y≡z a b c (original .a .b ¬a≡z aRb) (original .b .c ¬b≡z bRc) = original a c ¬a≡z (R-trans head a b c aRb bRc) 
    R'-trans head y z zRy ¬y≡z a b c (original .a .b ¬a≡z aRb) (y>z .b .c ¬b≡z bRy zPc) = y>z a c ¬a≡z (R-trans head a b y aRb bRy) zPc
    R'-trans head y z zRy ¬y≡z a b c (original .a .b ¬a≡z aRb) (zRz .b .c bRz c≡z) rewrite c≡z = original a z ¬a≡z (R-trans head a b z aRb bRz)
    R'-trans head y z zRy ¬y≡z a b c (original .a .b ¬a≡z aRb) (yRz .b .c bRy c≡z) = yRz a c (R-trans head a b y aRb bRy) c≡z
    R'-trans head y z zRy ¬y≡z a b c (y>z .a .b ¬a≡z aRy zPb) (zRx∧yRx→zR'x .b .c b≡z yPc zRc) = y>z a c ¬a≡z aRy λ cRz → yPc (R-trans head c z y cRz zRy) 
    R'-trans head y z zRy ¬y≡z a b c (y>z .a .b ¬a≡z aRy zPb) (original .b .c ¬b≡z bRc) = y>z a c ¬a≡z aRy λ cRz → zPb (R-trans head b c z bRc cRz)
    R'-trans head y z zRy ¬y≡z a b c (y>z .a .b ¬a≡z aRy zPb) (y>z .b .c ¬b≡z bRy zPc) = y>z a c ¬a≡z aRy zPc
    R'-trans head y z zRy ¬y≡z a b c (y>z .a .b ¬a≡z aRy zPb) (zRz .b .c bRz c≡z) = ⊥-elim (zPb bRz)
    R'-trans head y z zRy ¬y≡z a b c (y>z .a .b ¬a≡z aRy zPb) (yRz .b .c bRy c≡z) = yRz a c aRy c≡z
    R'-trans head y z zRy ¬y≡z a b c (zRz .a .b aRz b≡z) (zRx∧yRx→zR'x .b .c b≡z' yPc zRc) with a Fin.≟ z
    ... | false because ofⁿ ¬a≡z = original a c ¬a≡z (R-trans head a z c aRz zRc)
    ... | true because ofʸ a≡z = (zRx∧yRx→zR'x a c a≡z yPc zRc)
    R'-trans head y z zRy ¬y≡z a b c (zRz .a .b aRz b≡z) (original .b .c ¬b≡z bRc) = ⊥-elim (¬b≡z b≡z)
    R'-trans head y z zRy ¬y≡z a b c (zRz .a .b aRz b≡z) (y>z .b .c ¬b≡z bRy zPc) = ⊥-elim (¬b≡z b≡z)
    R'-trans head y z zRy ¬y≡z a b c (zRz .a .b aRz b≡z) (zRz .b .c bRz c≡z) = zRz a c aRz c≡z
    R'-trans head y z zRy ¬y≡z a b c (zRz .a .b aRz b≡z) (yRz .b .c bRy c≡z) = zRz a c aRz c≡z
    R'-trans head y z zRy ¬y≡z a b c (yRz .a .b aRy b≡z) (zRx∧yRx→zR'x .b .c _ yPc zRc) with a Fin.≟ z
    ... | false because ofⁿ ¬a≡z = original a c ¬a≡z (R-trans head a y c aRy (P→R {v = head} yPc))
    ... | true because ofʸ a≡z = (zRx∧yRx→zR'x a c a≡z yPc zRc)
    R'-trans head y z zRy ¬y≡z a b c (yRz .a .b aRy b≡z) (original .b .c ¬b≡z bRc) = ⊥-elim (¬b≡z b≡z)
    R'-trans head y z zRy ¬y≡z a b c (yRz .a .b aRy b≡z) (y>z .b .c ¬b≡z bRy zPc) = ⊥-elim (¬b≡z b≡z)
    R'-trans head y z zRy ¬y≡z a b c (yRz .a .b aRy b≡z) (zRz .b .c bRz c≡z) = yRz a c aRy c≡z
    R'-trans head y z zRy ¬y≡z a b c (yRz .a .b aRy b≡z) (yRz .b .c bRy c≡z) = yRz a c aRy c≡z

    R'-complete : {_R_ : Fin n → Fin n → Set} 
                → (head : Preference n n>2 _R_)
                → (y z : Fin n)
                → (zRy : z R y)
                → (¬y≡z : ¬ y ≡ z)
                → (a b : Fin n)
                → R' head y z ¬y≡z zRy a b ⊎ R' head y z ¬y≡z zRy b a
    R'-complete head y z zRy ¬y≡z a b with a Fin.≟ z 
    ... | false because ofⁿ ¬a≡z with R-dec head a b
    ... | inj₁ aRb = inj₁ (original a b ¬a≡z aRb)
    ... | inj₂ bPa with b Fin.≟ z
    ... | false because ofⁿ ¬b≡z = inj₂ (original b a ¬b≡z (P→R {v = head} bPa))
    ... | true because ofʸ b≡z with R-dec head a y 
    ... | inj₁ aRy rewrite b≡z = inj₁ (yRz a z aRy Eq.refl)
    ... | inj₂ yPa rewrite b≡z = inj₂ (zRx∧yRx→zR'x z a Eq.refl yPa (P→R {v = head} bPa))
    R'-complete head y z zRy ¬y≡z a b | true because ofʸ a≡z with b Fin.≟ z 
    ... | true because ofʸ b≡z = inj₁ (zRz a b (R-refl head a z a≡z) b≡z)
    ... | false because ofⁿ ¬b≡z with R-dec head b a 
    ... | inj₁ bRa = inj₂ (original b a ¬b≡z bRa)
    ... | inj₂ aPb with R-dec head b y 
    ... | inj₁ bRy = inj₂ (yRz b a bRy a≡z)
    ... | inj₂ yPb = inj₁ (zRx∧yRx→zR'x a b a≡z yPb (R-trans head z y b zRy (P→R {v = head} yPb)))
    
    R'-dec : {_R_ : Fin n → Fin n → Set} 
           → (head : Preference n n>2 _R_)
           → (y z : Fin n)
           → (zRy : z R y)
           → (¬y≡z : ¬ y ≡ z)
           → (a b : Fin n)
           → R' head y z ¬y≡z zRy a b ⊎ ¬ R' head y z ¬y≡z zRy a b
    R'-dec head y z zRy ¬y≡z a b with a Fin.≟ z  
    ... | false because ofⁿ ¬a≡z with R-dec head a b
    ... | inj₁ aRb = inj₁ (original a b ¬a≡z aRb)
    ... | inj₂ bPa with R-dec head z b
    ... | inj₂ bPz = inj₂ λ { (zRx∧yRx→zR'x .a .b a≡z yPb zRb) → ¬a≡z a≡z
                            ; (original .a .b ¬a≡z' aRb) → bPa aRb
                            ; (y>z .a .b ¬a≡z' aRy zPb) → bPz (P→R {v = head} zPb)
                            ; (zRz .a .b aRz b≡z) → bPz (R-refl head z b (Eq.sym b≡z))
                            ; (yRz .a .b aRy b≡z) → bPz (R-refl head z b (Eq.sym b≡z))} 
    ... | inj₁ zRb with R-dec head a y 
    ... | inj₂ yPa = inj₂ λ { (zRx∧yRx→zR'x .a .b a≡z yPb zRb) → ¬a≡z a≡z
                            ; (original .a .b ¬a≡z' aRb) → bPa aRb
                            ; (y>z .a .b ¬a≡z' aRy zPb) → yPa aRy
                            ; (zRz .a .b aRz b≡z) → bPa (R-trans head a z b aRz zRb)
                            ; (yRz .a .b aRy b≡z) → yPa aRy} 
    ... | inj₁ aRy with b Fin.≟ z
    ... | true because ofʸ b≡z = inj₁ (yRz a b aRy b≡z)
    ... | false because ofⁿ ¬b≡z with R-dec head b z 
    ... | inj₁ bRz = inj₂ λ { (zRx∧yRx→zR'x .a .b a≡z yPb zRb) → ¬a≡z a≡z
                            ; (original .a .b ¬a≡z' aRb) → bPa aRb
                            ; (y>z .a .b ¬a≡z' aRy zPb) → zPb bRz
                            ; (zRz .a .b aRz b≡z) → ¬b≡z b≡z
                            ; (yRz .a .b aRy b≡z) → ¬b≡z b≡z} 
    ... | inj₂ zPb = inj₁ (y>z a b ¬a≡z aRy zPb)
    R'-dec head y z ¬y≡z zRy a b | true because ofʸ a≡z with b Fin.≟ z
    ... | true because ofʸ b≡z = inj₁ (zRz a b (R-refl head a z a≡z) b≡z)
    ... | false because ofⁿ ¬b≡z with R-dec head z b 
    ... | inj₂ bPz = inj₂ (λ {(zRx∧yRx→zR'x .a .b _ yPb zRb) → bPz zRb
                            ; (original .a .b ¬a≡z aRb) → ¬a≡z a≡z
                            ; (y>z .a .b ¬a≡z aRy zPb) → ¬a≡z a≡z
                            ; (zRz .a .b aRz b≡z) → ¬b≡z b≡z
                            ; (yRz .a .b aRy b≡z) → ¬b≡z b≡z})
    ... | inj₁ zRb with R-dec head b y
    ... | inj₁ bRy = inj₂ (λ {(zRx∧yRx→zR'x .a .b _ yPb zRb) → yPb bRy
                            ; (original .a .b ¬a≡z aRb) → ¬a≡z a≡z
                            ; (y>z .a .b ¬a≡z aRy zPb) → ¬a≡z a≡z
                            ; (zRz .a .b aRz b≡z) → ¬b≡z b≡z
                            ; (yRz .a .b aRy b≡z) → ¬b≡z b≡z})
    ... | inj₂ yPb = inj₁ (zRx∧yRx→zR'x a b a≡z yPb zRb)

    P' : {_R_ : Fin n → Fin n → Set} 
       → (head : Preference n n>2 _R_)
       → (y z : Fin n) 
       → (zRy : z R y)
       → (¬y≡z : ¬ y ≡ z)
       → Preference n n>2 (R' head y z ¬y≡z zRy)
    P' head y z zRy ¬y≡z = record { R-trans    = R'-trans    head y z zRy ¬y≡z 
                                  ; R-complete = R'-complete head y z zRy ¬y≡z 
                                  ; R-dec      = R'-dec      head y z zRy ¬y≡z }

    agrees-x-z : {_R_ : Fin n → Fin n → Set} 
              → (head : Preference n n>2 _R_)
              → (x y z : Fin n) 
              → (P head y x) ⊎ (P head x z)
              → ¬ (x ≡ z) 
              → (¬y≡z : ¬ (y ≡ z))
              → (zRy : z R y)
              → R→Bool head x z ≡ R→Bool (P' head y z zRy ¬y≡z) x z
    agrees-x-z head x y z _ ¬x≡z ¬y≡z zRy with R-dec head x z | (R'-dec head y z zRy ¬y≡z) x z
    ... | inj₁ _ | inj₁ _ = Eq.refl
    ... | inj₁ xRz | inj₂ ¬xR'z = ⊥-elim (¬xR'z (original x z ¬x≡z xRz))
    ... | inj₂ zPx | inj₁ (zRx∧yRx→zR'x .x .z x≡z _ _) = ⊥-elim (¬x≡z x≡z)
    ... | inj₂ zPx | inj₁ (original .x .z _ xRz) = ⊥-elim (zPx xRz)
    ... | inj₂ zPx | inj₁ (y>z .x .z _ _ zPz) = ⊥-elim (zPz (R-refl head z z Eq.refl))
    ... | inj₂ zPx | inj₁ (zRz .x .z xRz _) = ⊥-elim (zPx xRz)
    ... | inj₂ _ | inj₂ _ = Eq.refl
    agrees-x-z head x y z (inj₁ yPx) ¬x≡z ¬y≡z zRy | inj₂ zPx | inj₁ (yRz .x .z xRy _) = ⊥-elim (yPx xRy)
    agrees-x-z head x y z (inj₂ xPz) ¬x≡z ¬y≡z zRy | inj₂ zPx | inj₁ (yRz .x .z xRy _) = ⊥-elim (xPz (P→R {v = head} zPx))
    
    agrees-x-y : {_R_ : Fin n → Fin n → Set} 
              → (head : Preference n n>2 _R_)
              → (x y z : Fin n)
              → ¬ (x ≡ z) 
              → (¬y≡z : ¬ (y ≡ z))
              → (zRy : z R y)
              → R→Bool (P' head y z zRy ¬y≡z) x y ≡ R→Bool head x y
    agrees-x-y head x y z ¬x≡z ¬y≡z zRy with R-dec head x y | (R'-dec head y z zRy ¬y≡z) x y
    ... | inj₁ _ | inj₁ _ = Eq.refl
    ... | inj₂ _ | inj₂ _ = Eq.refl
    ... | inj₁ xRy | inj₂ yP'x = ⊥-elim (yP'x (original x y ¬x≡z xRy))
    ... | inj₂ yPx | inj₁ (zRx∧yRx→zR'x .x .y x≡z _ _) = ⊥-elim (¬x≡z x≡z)
    ... | inj₂ yPx | inj₁ (original .x .y ¬x≡z xRy) = ⊥-elim (yPx xRy)
    ... | inj₂ yPx | inj₁ (y>z .x .y ¬x≡z xRy zPy) = ⊥-elim (yPx xRy)
    ... | inj₂ yPx | inj₁ (zRz .x .y xRz y≡z) = ⊥-elim (¬y≡z y≡z)
    ... | inj₂ yPx | inj₁ (yRz .x .y xRy y≡z) = ⊥-elim (yPx xRy)

... | inj₂ yPz = _R_ , head , Eq.refl , Eq.refl , yPz

LemmaTwoSimilar : (m : ℕ) 
                → (c : Coalition m) 
                → (v : Votes n n>2 m) 
                → (x y z : Fin n) 
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z) 
                → (CoalitionAgrees x y c v) 
                → (CoalitionAgrees y x (InverseCoalition c) v)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n n>2 m) λ v' 
                                    → (Similar m x z (Zipped n>2 x z v v')  
                                    × Similar m x y (Zipped n>2 x y v' v)
                                    × ElectionAgrees v' y z)
LemmaTwoSimilar zero [] [] x y z ¬x≡z ¬y≡z _ _ _ = [] , (tt , (tt , tt))
LemmaTwoSimilar (suc m) (false ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (false-agrees .c .rem ca-x>y .head) 
                (true-agrees .(InverseCoalition c) .rem in-ca-y>x .head yPx)
                (false-agrees .c .rem ca-x>z .head) 
    with LemmaTwoSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z
... | sim-coal , is-sim-xz , is-sim-xy , sim-y>z  
    with LemmaTwoAlter head x y z (inj₁ yPx) ¬x≡z ¬y≡z
... | _ , p' , p'-sim-xz , p'-sim-xy , ¬zR'y = (p' ∷ sim-coal) , (p'-sim-xz , is-sim-xz) , (p'-sim-xy , is-sim-xy) , (¬zR'y , sim-y>z)
LemmaTwoSimilar (suc m) (true ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (true-agrees .c .rem ca-x>y .head xPz) 
                (false-agrees .(InverseCoalition c) .rem in-ca-y>x .head)
                (true-agrees .c .rem ca-x>z .head xPy)
    with LemmaTwoSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z 
... | sim-coal , is-sim-xz , is-sim-xy , sim-y>z 
    with LemmaTwoAlter head x y z (inj₂ xPy) ¬x≡z ¬y≡z
... | _ , p' , p'-sim-xz , p'-sim-xy , ¬zR'y = (p' ∷ sim-coal) , (p'-sim-xz , is-sim-xz) , (p'-sim-xy , is-sim-xy) , (¬zR'y , sim-y>z)
    
LemmaTwo : (m : ℕ) → (c : Coalition m) → (v : Votes n n>2 m) → (x y z : Fin n) → ¬ (x ≡ z) → ¬ (y ≡ z) → Decisive-a>b c v x y → StrictlyDecisive-a>b c v x z 
LemmaTwo m c v x y z ¬x≡z ¬y≡z (dec-a>b ca-x>y in-ca-y>x swfx>y) ca-x>z  
  with LemmaTwoSimilar m c v x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z                                                       
... | v' , v'-sim-xz , v-sim-xy , v'-y>z = BinaryIIA x z v' v'-sim-xz (Transitivity x y z (BinaryIIA x y v v-sim-xy swfx>y) (Pareto y z v'-y>z))     

StrictlyDecisive-x>x : {m n : ℕ} → {n>2 : n ℕ.> 2}
             → (c : NonEmptyCoalition m)
             → (v : Votes n n>2 m) 
             → (a b : Fin n)
             → (a ≡ b)
             → StrictlyDecisive-a>b (Unwrap c) v a b 
StrictlyDecisive-x>x c v a b a≡b = λ ca → ⊥-elim (helper v c a b a≡b ca)
  where
    helper : {m n : ℕ} → {n>2 : n ℕ.> 2} 
           → (v : Votes n n>2 m) 
           → (c : NonEmptyCoalition m) 
           → (a b : Fin n) 
           → (a ≡ b) 
           → (CoalitionAgrees a b (Unwrap c) v)
           → ⊥
    helper (p ∷ v) (.true ∷ c , zero , _) a b a≡b (true-agrees .c .v ca .p aPb) = ⊥-elim (aPb (R-refl p b a (Eq.sym a≡b)))
    helper (p ∷ v) (.(false ∷ c) , suc fst , snd) a b a≡b (false-agrees c .v ca .p) = helper v (c , (fst , snd)) a b a≡b ca
    helper (p ∷ v) (.(true ∷ c) , suc fst , snd) a b a≡b (true-agrees c .v ca .p aPb) = ⊥-elim (aPb (R-refl p b a (Eq.sym a≡b)))

FreshCandidate : (n : ℕ) → (n>2 : n ℕ.> 2) (a b : Fin n) → Σ (Fin n) λ c → ¬ (a ≡ c) × ¬ (b ≡ c)
FreshCandidate (suc zero) (s≤s ()) a b
FreshCandidate (suc (suc zero)) (s≤s (s≤s ())) a b
FreshCandidate (suc (suc (suc n))) n>2 zero zero = (suc zero) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 zero (suc zero) = (suc (suc zero)) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 zero (suc (suc b)) =  (suc zero) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc zero) zero = (suc (suc zero)) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc a) (suc b) = zero , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc (suc a)) zero = (suc zero) , ((λ {()}) , (λ {()}))

CorollaryOne : (m : ℕ) 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n n>2 m) 
             → (x y w : Fin n) 
             → Decisive-a>b (Unwrap c) v x y 
             → StrictlyDecisive-a>b (Unwrap c) v x w
CorollaryOne  zero c [] x y w (dec-a>b ca-x>y in-ca-y>x swfx>y) = λ _ → Pareto x w tt
CorollaryOne {n} {n>2} (suc m) c v x y w (dec-a>b ca-x>y in-ca-y>x swfx>y) with x Fin.≟ w 
... | false because ofⁿ ¬x≡w with y Fin.≟ w
... | false because ofⁿ ¬y≡w = LemmaTwo (suc m) (Unwrap c) v x y w ¬x≡w ¬y≡w (dec-a>b ca-x>y in-ca-y>x swfx>y)
... | true because ofʸ y≡w rewrite y≡w = λ _ → swfx>y
CorollaryOne (suc m) c v x y w (dec-a>b ca-x>y in-ca-y>x swfx>y) 
  | true because ofʸ x≡w = StrictlyDecisive-x>x c v x w x≡w

LemmaThreeAlter : {_R_ : Fin n → Fin n → Set} 
              → (head : Preference n n>2 _R_)
              → (x y z : Fin n) 
              → (P head y x) ⊎ (P head z y)
              → ¬ (x ≡ z) 
              → ¬ (y ≡ z)
              → Σ (Fin n → Fin n → Set) λ _R'_ → Σ (Preference n n>2 _R'_) λ P' → R→Bool head z y ≡ R→Bool P' z y × R→Bool P' x y ≡ R→Bool head x y × P P' z x
LemmaThreeAlter {_R_ = _R_} head x y z yPx⊎zPy ¬x≡z ¬y≡z = {!   !}

LemmaThreeSimilar : (m : ℕ) 
                → (c : Coalition m) 
                → (v : Votes n n>2 m) 
                → (x y z : Fin n) 
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z) 
                → (CoalitionAgrees x y c v) 
                → (CoalitionAgrees y x (InverseCoalition c) v)
                → (CoalitionAgrees z y c v)
                → Σ (Votes n n>2 m) λ v' 
                                    → (Similar m z y (Zipped n>2 z y v v')  
                                    × Similar m x y (Zipped n>2 x y v' v)
                                    × ElectionAgrees v' z x)
LemmaThreeSimilar zero [] [] x y z ¬x≡z ¬y≡z _ _ _ = [] , (tt , (tt , tt))
LemmaThreeSimilar (suc m) (false ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (false-agrees .c .rem ca-x>y .head) 
                (true-agrees .(InverseCoalition c) .rem in-ca-y>x .head yPx)
                (false-agrees .c .rem ca-z>y .head) 
    with LemmaThreeSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-z>y
... | sim-coal , is-sim-zy , is-sim-xy , sim-z>x 
    with LemmaThreeAlter head x y z (inj₁ yPx) ¬x≡z ¬y≡z 
... | _ , p' , p'-sim-zy , p'-sim-xy , ¬xR'z = (p' ∷ sim-coal) , (p'-sim-zy , is-sim-zy) , (p'-sim-xy , is-sim-xy) , (¬xR'z , sim-z>x)
LemmaThreeSimilar (suc m) (true ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (true-agrees .c .rem ca-x>y .head xPy) 
                (false-agrees .(InverseCoalition c) .rem in-ca-y>x .head)
                (true-agrees .c .rem ca-z>y .head zPy)
    with LemmaThreeSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-z>y
... | sim-coal , is-sim-zy , is-sim-xy , sim-z>x     
    with LemmaThreeAlter head x y z (inj₂ zPy) ¬x≡z ¬y≡z 
... | _ , p' , p'-sim-zy , p'-sim-xy , ¬xR'z = (p' ∷ sim-coal) , (p'-sim-zy , is-sim-zy) , (p'-sim-xy , is-sim-xy) , (¬xR'z , sim-z>x)


LemmaThree : (m : ℕ) → (c : Coalition m) → (v : Votes n n>2 m) → (x y z : Fin n) → ¬ (x ≡ z) → ¬ (y ≡ z) → Decisive-a>b c v x y → StrictlyDecisive-a>b c v z y 
LemmaThree m c v x y z ¬x≡z ¬y≡z (dec-a>b ca-x>y in-ca-y>x swfx>y) ca-z>y
  with LemmaThreeSimilar m c v x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-z>y
... | v' , v'-sim-zy , v'-sim-xy , v'-z>x = BinaryIIA z y v' v'-sim-zy (Transitivity z x y (Pareto z x v'-z>x) (BinaryIIA x y v v'-sim-xy swfx>y))

CorollaryTwo : (m : ℕ) 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n n>2 m) 
             → (x y w : Fin n) 
             → Decisive-a>b (Unwrap c) v x y 
             → StrictlyDecisive-a>b (Unwrap c) v w y
CorollaryTwo zero c [] x y w (dec-a>b ca-x>y in-ca-y>x swfx>y) = λ _ → Pareto w y tt
CorollaryTwo {n} {n>2} (suc m) c v x y w (dec-a>b ca-x>y in-ca-y>x swfx>y) with y Fin.≟ w 
... | false because ofⁿ ¬y≡w with x Fin.≟ w
... | false because ofⁿ ¬x≡w = LemmaThree (suc m) (Unwrap c) v x y w ¬x≡w ¬y≡w (dec-a>b ca-x>y in-ca-y>x swfx>y)
... | true because ofʸ y≡w rewrite y≡w = λ _ → swfx>y
CorollaryTwo (suc m) c v x y w (dec-a>b ca-x>y in-ca-y>x swfx>y) 
  | true because ofʸ y≡w = StrictlyDecisive-x>x c v w y (Eq.sym y≡w) 

LemmaFourAlter : {_R_ : Fin n → Fin n → Set} 
              → (head : Preference n n>2 _R_)
              → (x y v w : Fin n)  
              → ¬ (x ≡ v) 
              → ¬ (y ≡ w)
              → Σ (Fin n → Fin n → Set) λ _R'_ 
                → Σ (Preference n n>2 _R'_) λ P' 
                  → R→Bool head v w ≡ R→Bool P' v w
                  × R→Bool P' x y ≡ R→Bool head x y 
                  × P P' v x
                  × P P' y w
LemmaFourAlter {_R_ = _R_} head x y v w = {!   !}

LemmaFourSimilar : (m : ℕ) 
                → (c : Coalition m) 
                → (ballots : Votes n n>2 m) 
                → (x y v w : Fin n) 
                → ¬ (x ≡ v) 
                → ¬ (y ≡ w)
                → (CoalitionAgrees x y c ballots) 
                → (CoalitionAgrees y x (InverseCoalition c) ballots)
                → Σ (Votes n n>2 m) λ ballots' 
                                    → (Similar m v w (Zipped n>2 v w ballots ballots')
                                    ×  Similar m x y (Zipped n>2 x y ballots' ballots)
                                    × ElectionAgrees ballots' v x
                                    × ElectionAgrees ballots' y w)
LemmaFourSimilar m c [] x y v w _ _ _ _ = [] , tt , tt , tt , tt
LemmaFourSimilar (suc m') (false ∷ c) (p ∷ ballots) x y v w ¬x≡v ¬y≡w
  (false-agrees .c .ballots ca-x>y .p) 
  (true-agrees .(InverseCoalition c) .ballots ca-y>x .p x₁) with
  LemmaFourSimilar m' c ballots x y v w ¬x≡v ¬y≡w ca-x>y ca-y>x 
... | alt-ballots , sim-v>w , sim-x>y , v>x , y>w with
  LemmaFourAlter p x y v w ¬x≡v ¬y≡w
... | _ , P' , p'-same-vw , p'-same-xy , p'-v>x , p'-y>w = 
      (P' ∷ alt-ballots) 
    , (p'-same-vw , sim-v>w) 
    , (p'-same-xy , sim-x>y) 
    , (p'-v>x , v>x) 
    , (p'-y>w , y>w)
LemmaFourSimilar (suc m') (true ∷ c) (p ∷ ballots) x y v w ¬x≡v ¬y≡w
  (true-agrees .c .ballots ca-x>y .p x₁) 
  (false-agrees .(InverseCoalition c) .ballots ca-y>x .p) with
  LemmaFourSimilar m' c ballots x y v w ¬x≡v ¬y≡w ca-x>y ca-y>x
... | alt-ballots , sim-v>w , sim-x>y , v>x , y>w with
  LemmaFourAlter p x y v w ¬x≡v ¬y≡w
... | _ , P' , p'-same-vw , p'-same-xy , p'-v>x , p'-y>w = 
      (P' ∷ alt-ballots) 
    , (p'-same-vw , sim-v>w) 
    , (p'-same-xy , sim-x>y) 
    , (p'-v>x , v>x) 
    , (p'-y>w , y>w)

LemmaFour : (m : ℕ) 
          → (c : NonEmptyCoalition m) 
          → (ballots : Votes n n>2 m) 
          → (x y : Fin n) 
          → Decisive-a>b (Unwrap c) ballots x y
          → Decisive (Unwrap c) ballots
LemmaFour m c ballots x y (dec-a>b c-x>y inv-y>x swf-x-y) v w with x Fin.≟ v
... | true because ofʸ x≡v rewrite x≡v = CorollaryOne m c ballots v y w (dec-a>b c-x>y inv-y>x swf-x-y)
... | false because ofⁿ ¬x≡v with y Fin.≟ w 
...   | true because ofʸ y≡w rewrite y≡w = CorollaryTwo m c ballots x w v (dec-a>b c-x>y inv-y>x swf-x-y)
...   | false because ofⁿ ¬y≡w with LemmaFourSimilar m (Unwrap c) ballots x y v w ¬x≡v ¬y≡w c-x>y inv-y>x 
...   | ballots' , sim-v>w , sim-x>y , v>x , y>w = 
      λ _ → BinaryIIA v w ballots' sim-v>w 
            (Transitivity v x w (Pareto v x v>x) (Transitivity x y w 
              (BinaryIIA x y ballots sim-x>y swf-x-y) (Pareto y w y>w)))

-- contraction of decisive sets
LemmaFive : (m : ℕ) 
         → (c : Coalition m) 
         → (ballots : Votes n n>2 m)
         → Decisive c ballots
         → Σ (Coalition m) 
              λ c → SingletonCoalition c 
                  × Decisive c ballots
LemmaFive m c ballots dec = {!   !}

-- we have decisive set G
-- 2 cases:
-- G is of length one -- done
-- G is of length > 1
--    split G into two subsets
--    first subset is singleton coalition of the head
--    second subset is the tail
--    G1 has x > y > z
--    G2 has z > x > y
--    ∉ G has y > z > x
--    case on the result of the election, either G1 or G2 must be decisive
--    does this require elections to be preferences? i think that's probably fine

-- could also just do the ultrafilter thing

ArrowsTheorem : (m : ℕ) 
              → (ballots : Votes n n>2 m)
              → Σ (Coalition m) 
                  λ c → SingletonCoalition c 
                      × Decisive c ballots
ArrowsTheorem m ballots = LemmaFive m (Whole m) ballots (LemmaOne m ballots)