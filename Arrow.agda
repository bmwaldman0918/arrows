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
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
  variable
    n : ℕ
    n>1 : n ℕ.> 1

-- the coalition of the whole is decisive

LemmaOne : (m : ℕ) → (v : Votes n n>1 m) → (a b : Fin n) → CoalitionAgrees a b (Whole m) v → SWF v a b
LemmaOne m v a b c = Pareto a b (helper m v a b c) where
  helper : (m : ℕ) → (v : Votes n n>1 m) → (a b : Fin n) → CoalitionAgrees a b (Whole m) v → ElectionAgrees v a b
  helper .0 [] a b c = tt
  helper (suc m) (x ∷ v) a b (true-agrees .(Whole m) .v c .x agrees) = agrees , (helper m v a b c)

LemmaTwoAlter : {_R_ : Fin n → Fin n → Set} 
              → (head : Preference n n>1 _R_)
              → (x y z : Fin n) 
              → ¬ (x ≡ z) 
              → ¬ (y ≡ z)
              → Σ (Fin n → Fin n → Set) λ _R'_ → Σ (Preference n n>1 _R'_) λ P' → R→Bool head x z ≡ R→Bool P' x z × R→Bool P' x y ≡ R→Bool head x y × P P' y z
LemmaTwoAlter {_R_ = _R_} head x y z ¬x≡z ¬y≡z with R-dec head z y
... | inj₁ zRy = R' head y z ¬y≡z , P' head y z ¬y≡z , {!   !} , {!   !} , λ {(y>z .z .y _ yPy _) → yPy (R-refl head y y Eq.refl)
                                                                            ; (original .z .y ¬z≡z _) → ¬z≡z Eq.refl
                                                                            ; (swap-y .z .y z≡y x₁) → ¬y≡z (Eq.sym z≡y)
                                                                            ; (zRz .z .y _ y≡z) → ¬y≡z y≡z}
  where
    data R' {_R_ : Fin n → Fin n → Set} 
            (head : Preference n n>1 _R_) 
            (y z : Fin n) 
            (¬y≡z : ¬ y ≡ z) : Fin n → Fin n → Set where

        zRx∧yRx→zR'x : (a b : Fin n) 
                     → (a ≡ z)
                     → P head y b
                     → z R b
                     → R' head y z ¬y≡z a b

        original  : (a b : Fin n) 
                  → ¬ (a ≡ z)
                  → a R b 
                  → R' head y z ¬y≡z a b

        y>z       : (a b : Fin n) 
                  → (a R y)
                  → (z R b) 
                  → R' head y z ¬y≡z a b

    R'-trans : {_R_ : Fin n → Fin n → Set} 
           → (head : Preference n n>1 _R_)
           → (y z : Fin n)
           → (¬y≡z : ¬ y ≡ z)
           → (a b c : Fin n)
           → R' head y z ¬y≡z a b 
           → R' head y z ¬y≡z b c 
           → R' head y z ¬y≡z a c
    R'-trans head y z ¬y≡z a b c (y>z .a .b a≡z yPb zRb) (y>z .b .c b≡z yPc zRc) = y>z a c a≡z yPc zRc
    R'-trans head y z ¬y≡z a b c (y>z .a .b a≡z yPb zRb) (original .b .c ¬b≡z bRc) = y>z a c a≡z (λ cRy → yPb (R-trans head b c y bRc cRy)) (R-trans head z b c zRb bRc)
    R'-trans head y z ¬y≡z a b c (y>z .a .b a≡z yPb zRb) (swap-y .b .c b≡y zRc) rewrite b≡y = ⊥-elim (yPb (R-refl head y y Eq.refl))
    R'-trans head y z ¬y≡z a b c (y>z .a .b a≡z yPb zRb) (zRz .b .c b≡z c≡z) = zRz a c a≡z c≡z
    R'-trans head y z ¬y≡z a b c (original .a .b ¬a≡z aRb) (y>z .b .c b≡z yPc zRc) rewrite (Eq.sym b≡z) = original a c ¬a≡z (R-trans head a b c aRb zRc)
    R'-trans head y z ¬y≡z a b c (original .a .b ¬a≡z aRb) (original .b .c ¬b≡z bRc) = original a c ¬a≡z (R-trans head a b c aRb bRc)
    R'-trans head y z ¬y≡z a b c (original .a .b ¬a≡z aRb) (swap-y .b .c b≡y zRc) rewrite Eq.sym b≡y = original a c ¬a≡z (R-trans head a b c aRb {! R-trans head b   !})
    R'-trans head y z ¬y≡z a b c (original .a .b ¬a≡z aRb) (zRz .b .c b≡z c≡z) rewrite (Eq.sym c≡z) | (Eq.sym b≡z) = (original a b ¬a≡z aRb)
    R'-trans head y z ¬y≡z a b c (swap-y .a .b a≡y zRb) (y>z .b .c b≡z yPc zRc) = swap-y a c a≡y zRc
    R'-trans head y z ¬y≡z a b c (swap-y .a .b a≡y zRb) (original .b .c ¬b≡z bRc) = swap-y a c a≡y (R-trans head z b c zRb bRc)
    R'-trans head y z ¬y≡z a b c (swap-y .a .b a≡y zRb) (swap-y .b .c b≡y zRc) = swap-y a c a≡y zRc
    R'-trans head y z ¬y≡z a b c (swap-y .a .b a≡y zRb) (zRz .b .c b≡z c≡z) = swap-y a c a≡y (R-refl head z c (Eq.sym c≡z))
    R'-trans head y z ¬y≡z a b c (zRz .a .b a≡z b≡z) (y>z .b .c _ yPc zRc) = y>z a c a≡z yPc zRc
    R'-trans head y z ¬y≡z a b c (zRz .a .b a≡z b≡z) (original .b .c ¬b≡z bRc) = ⊥-elim (¬b≡z b≡z)
    R'-trans head y z ¬y≡z a b c (zRz .a .b a≡z b≡z) (swap-y .b .c b≡y zRc) = ⊥-elim (¬y≡z (Eq.trans (Eq.sym b≡y) b≡z))
    R'-trans head y z ¬y≡z a b c (zRz .a .b a≡z b≡z) (zRz .b .c _ c≡z) = zRz a c a≡z c≡z

    R'-complete : {_R_ : Fin n → Fin n → Set} 
                → (head : Preference n n>1 _R_)
                → (y z : Fin n) 
                → (¬y≡z : ¬ y ≡ z)
                → (a b : Fin n)
                → R' head y z ¬y≡z a b ⊎ R' head y z ¬y≡z b a
    R'-complete head y z ¬y≡z a b with a Fin.≟ z 
    ... | false because ofⁿ ¬a≡z with R-dec head a b
    ... | inj₁ aRb = inj₁ (original a b ¬a≡z aRb)
    ... | inj₂ bPa with b Fin.≟ z
    ... | false because ofⁿ ¬b≡z = inj₂ (original b a ¬b≡z (P→R {v = head} bPa))
    ... | true because ofʸ b≡z with R-dec head a y 
    ... | inj₂ aPy rewrite b≡z = inj₂ (y>z z a Eq.refl aPy (P→R {v = head} bPa))
    ... | inj₁ yRa = inj₁ {!   !}
    R'-complete head y z ¬y≡z a b | true because ofʸ a≡z = {!   !}
    
    R'-dec : {_R_ : Fin n → Fin n → Set} 
           → (head : Preference n n>1 _R_)
           → (y z : Fin n)
           → (¬y≡z : ¬ y ≡ z)
           → (a b : Fin n)
           → R' head y z ¬y≡z a b ⊎ ¬ R' head y z ¬y≡z a b
    R'-dec head y z ¬y≡z a b with a Fin.≟ z  
    ... | false because ofⁿ ¬a≡z with R-dec head a b
    ... | inj₁ aRb = inj₁ (original a b ¬a≡z aRb)
    ... | inj₂ bPa with a Fin.≟ y 
    ... | false because ofⁿ ¬a≡y = inj₂ (λ {(y>z .a .b a≡z _ _) → ¬a≡z a≡z
                                          ; (original .a .b _ aRb) → bPa aRb
                                          ; (swap-y .a .b a≡y _) → ¬a≡y a≡y
                                          ; (zRz .a .b a≡z _) → ¬a≡z a≡z})
    ... | true because ofʸ a≡y with R-dec head z b 
    ... | inj₁ zRb = inj₁ (swap-y a b a≡y zRb)
    ... | inj₂ bPz = inj₂ (λ {(y>z .a .b a≡z _ _) → ¬a≡z a≡z
                              ; (original .a .b _ aRb) → bPa aRb
                              ; (swap-y .a .b _ zRb) → bPz zRb
                              ; (zRz .a .b a≡z _) → ¬a≡z a≡z})
    R'-dec head y z ¬y≡z a b | true because ofʸ a≡z with b Fin.≟ z
    ... | true because ofʸ b≡z = inj₁ (zRz a b a≡z b≡z) 
    ... | false because ofⁿ ¬b≡z with R-dec head z b 
    ... | inj₂ bPz = inj₂ (λ {(y>z .a .b _ _ zRb) → bPz zRb
                            ; (original .a .b ¬a≡z _) → ¬a≡z a≡z
                            ; (swap-y .a .b a≡y zRb) → bPz zRb
                            ; (zRz .a .b _ b≡z) → ¬b≡z b≡z})
    ... | inj₁ zRb with R-dec head b y
    ... | inj₁ bRy = inj₂ (λ {(y>z .a .b _ yPb _) → yPb bRy
                            ; (original .a .b ¬a≡z _) → ¬a≡z a≡z
                            ; (swap-y .a .b a≡y _) → ¬y≡z (Eq.trans (Eq.sym a≡y) a≡z)
                            ; (zRz .a .b _ b≡z) → ¬b≡z b≡z})
    ... | inj₂ yPb = inj₁ (y>z a b a≡z yPb zRb)

     {- with a Fin.≟ y | b Fin.≟ z
    ... | true because ofʸ a≡y | true because ofʸ b≡z = inj₁ (y>z a b a≡y b≡z)
    R'-dec head x y z a b | false because ofⁿ ¬a≡y | b≟z with R-dec head a b
    ... | inj₂ ¬aRb = inj₂ λ {(y>z .a .b a≡y b≡z) → ¬a≡y a≡y
                             ; (original .a .b _ aRb) → ¬aRb aRb}
    ... | inj₁ aRb with a Fin.≟ z | b Fin.≟ y
    ... | false because ofⁿ ¬a≡z | b≟y = inj₁ (original a b (inj₁ ¬a≡z) aRb)
    ... | a≟z | false because ofⁿ ¬b≡y = inj₁ (original a b (inj₂ ¬b≡y) aRb)
    ... | true because ofʸ a≡z | true because ofʸ b≡y = inj₂ (λ {(y>z .a .b a≡y b≡z) → ¬a≡y a≡y
                                                                ; (original .a .b (inj₁ ¬a≡z) _) → ¬a≡z a≡z
                                                                ; (original .a .b (inj₂ ¬b≡y) _) → ¬b≡y b≡y})
    R'-dec head x y z a b | a≟y | false because ofⁿ ¬b≡z with R-dec head a b 
    ... | inj₂ ¬aRb = inj₂ (λ {(y>z .a .b a≡y b≡z) → ¬b≡z b≡z
                             ; (original .a .b _ aRb) → ¬aRb aRb}) 
    ... | inj₁ aRb with a Fin.≟ z | b Fin.≟ y 
    ... | false because ofⁿ ¬a≡z | b≟y = inj₁ (original a b (inj₁ ¬a≡z) aRb)
    ... | a≟z | false because ofⁿ ¬b≡y = inj₁ (original a b (inj₂ ¬b≡y) aRb)
    ... | true because ofʸ a≡z | true because ofʸ b≡y = inj₂ (λ {(y>z .a .b a≡y b≡z) → ¬b≡z b≡z
                                                                ; (original .a .b (inj₁ ¬a≡z) _) → ¬a≡z a≡z
                                                                ; (original .a .b (inj₂ ¬b≡y) _) → ¬b≡y b≡y})
    -}
    P' : {_R_ : Fin n → Fin n → Set} 
       → (head : Preference n n>1 _R_)
       → (y z : Fin n) 
       → (¬y≡z : ¬ y ≡ z)
       → Preference n n>1 (R' head y z ¬y≡z)
    P' head y z ¬y≡z = record { R-trans    = R'-trans    head y z ¬y≡z 
                                     ; R-complete = R'-complete head y z ¬y≡z 
                                     ; R-dec      = R'-dec      head y z ¬y≡z }
    
... | inj₂ yPz = _R_ , head , Eq.refl , Eq.refl , yPz

LemmaTwoSimilar : (m : ℕ) 
                → (c : Coalition m) 
                → (v : Votes n n>1 m) 
                → (x y z : Fin n) 
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z) 
                → (CoalitionAgrees x y c v) 
                → (CoalitionAgrees y x (InverseCoalition c) v)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n n>1 m) λ v' 
                                    → (Similar m x z (Zipped n>1 x z v v')  
                                    × Similar m x y (Zipped n>1 x y v' v)
                                    × ElectionAgrees v' y z)
LemmaTwoSimilar zero [] [] x y z ¬x≡z ¬y≡z _ _ _ = [] , (tt , (tt , tt))
LemmaTwoSimilar (suc m) (false ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (false-agrees .c .rem ca-x>y .head) 
                (true-agrees .(InverseCoalition c) .rem in-ca-y>x .head ¬xRy)
                (false-agrees .c .rem ca-x>z .head) 
    with LemmaTwoSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z
... | sim-coal , is-sim-xz , is-sim-xy , sim-y>z  
    with LemmaTwoAlter head x y z ¬x≡z ¬y≡z
... | _ , p' , p'-sim-xz , p'-sim-xy , ¬zR'y = (p' ∷ sim-coal) , (p'-sim-xz , is-sim-xz) , (p'-sim-xy , is-sim-xy) , (¬zR'y , sim-y>z)
LemmaTwoSimilar (suc m) (true ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (true-agrees .c .rem ca-x>y .head x₁) 
                (false-agrees .(InverseCoalition c) .rem in-ca-y>x .head)
                (true-agrees .c .rem ca-x>z .head x₂)
    with LemmaTwoSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z 
... | sim-coal , is-sim-xz , is-sim-xy , sim-y>z 
    with LemmaTwoAlter head x y z ¬x≡z ¬y≡z
... | _ , p' , p'-sim-xz , p'-sim-xy , ¬zR'y = (p' ∷ sim-coal) , (p'-sim-xz , is-sim-xz) , (p'-sim-xy , is-sim-xy) , (¬zR'y , sim-y>z)

LemmaTwo : (m : ℕ) → (c : Coalition m) → (v : Votes n n>1 m) → (x y z : Fin n) → ¬ (x ≡ z) → ¬ (y ≡ z) → Decisive-a>b c v x y → StrictlyDecisive-a>b c v x z 
LemmaTwo m c v x y z ¬x≡z ¬y≡z (dec-a>b ca-x>y in-ca-y>x swfx>y) ca-x>z  
  with LemmaTwoSimilar m c v x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z                                                  
... | v' , v'-sim-xz , v-sim-xy , v'-y>z = BinaryIIA x z v' v'-sim-xz (Transitivity x y z (BinaryIIA x y v v-sim-xy swfx>y) (Pareto y z v'-y>z))    