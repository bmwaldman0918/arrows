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
... | inj₁ zRy = R' head x y z ¬x≡z ¬y≡z , P' head x y z ¬x≡z ¬y≡z , {!   !} , {!   !} , λ {(y>z .z .y _ y≡z) → ¬y≡z y≡z
                                                                                          ; (original .z .y ¬z≡z _ _) → ¬z≡z Eq.refl
                                                                                          ; (swap-y .z .y z≡y _) → ¬y≡z (Eq.sym z≡y)
                                                                                          ; (swap-z .z .y _ _ yPy) → yPy (R-refl head y y Eq.refl)}
  where
    data R' {_R_ : Fin n → Fin n → Set} 
            (head : Preference n n>1 _R_) 
            (x y z : Fin n) 
            (¬x≡z : ¬ x ≡ z) 
            (¬y≡z : ¬ y ≡ z) : Fin n → Fin n → Set where
        y>z       : (a b : Fin n) 
                  → (a ≡ y)
                  → (b ≡ z)
                  → R' head x y z ¬x≡z ¬y≡z a b
        original  : (a b : Fin n) 
                  → ¬ (a ≡ z)
                  → ¬ (b ≡ y)
                  → a R b
                  → R' head x y z ¬x≡z ¬y≡z a b
        swap-y    : (a b : Fin n)
                  → (a ≡ y)
                  → z R b
                  → R' head x y z ¬x≡z ¬y≡z a b
        swap-z    : (a b : Fin n)
                  → (a ≡ z)
                  → a R b
                  → P head y b
                  → R' head x y z ¬x≡z ¬y≡z a b
    R'-trans : {_R_ : Fin n → Fin n → Set} 
           → (head : Preference n n>1 _R_)
           → (x y z : Fin n)
           → (¬x≡z : ¬ x ≡ z) 
           → (¬y≡z : ¬ y ≡ z)
           → (a b c : Fin n)
           → R' head x y z ¬x≡z ¬y≡z a b 
           → R' head x y z ¬x≡z ¬y≡z b c 
           → R' head x y z ¬x≡z ¬y≡z a c
    R'-trans head x y z ¬x≡z ¬y≡z a b c (y>z .a .b a≡y b≡z) (y>z .b .c b≡y c≡z) = y>z a c a≡y  c≡z
    R'-trans head x y z ¬x≡z ¬y≡z a b c (y>z .a .b a≡y b≡z) (original .b .c ¬b≡z ¬c≡y bRc) = ⊥-elim (¬b≡z b≡z)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (y>z .a .b a≡y b≡z) (swap-y .b .c b≡y zRc) = ⊥-elim (¬y≡z (Eq.trans (Eq.sym b≡y) b≡z))
    R'-trans head x y z ¬x≡z ¬y≡z a b c (y>z .a .b a≡y b≡z) (swap-z .b .c b≡z' bRc yPc) rewrite a≡y = original y c ¬y≡z (λ c≡y → P↛≡ {v = head} yPc (Eq.sym c≡y)) (P→R {v = head} yPc)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (original .a .b ¬a≡z ¬b≡y aRb) (y>z .b .c b≡y c≡z) = ⊥-elim (¬b≡y b≡y)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (original .a .b ¬a≡z ¬b≡y aRb) (original .b .c ¬b≡z ¬c≡y bRc) = original a c ¬a≡z ¬c≡y (R-trans head a b c aRb bRc)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (original .a .b ¬a≡z ¬b≡y aRb) (swap-y .b .c b≡y aRb') = ⊥-elim (¬b≡y b≡y)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (original .a .b ¬a≡z ¬b≡y aRb) (swap-z .b .c b≡z bRc yPc) = original a c ¬a≡z (λ c≡y → P↛≡ {v = head} yPc (Eq.sym c≡y)) (R-trans head a b c aRb bRc)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-y .a .b a≡y zRb) (y>z .b .c b≡y c≡z) = y>z a c a≡y c≡z
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-y .a .b a≡y zRb) (original .b .c ¬b≡z ¬c≡y bRc) = swap-y a c a≡y (R-trans head z b c zRb bRc)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-y .a .b a≡y zRb) (swap-y .b .c b≡y zRc) = swap-y a c a≡y zRc
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-y .a .b a≡y zRb) (swap-z .b .c b≡z bRc yPc) = swap-y a c a≡y (R-trans head z b c zRb bRc)
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-z .a .b a≡z aRb yPb) (y>z .b .c b≡y c≡z) = ⊥-elim (yPb (R-refl head b y b≡y)) 
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-z .a .b a≡z aRb yPb) (original .b .c ¬b≡z ¬c≡y bRc) = swap-z a c a≡z (R-trans head a b c aRb bRc) (λ cRy → yPb (R-trans head b c y bRc cRy))
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-z .a .b a≡z aRb yPb) (swap-y .b .c b≡y zRc) rewrite a≡z = ⊥-elim (yPb (R-refl head b y b≡y))
    R'-trans head x y z ¬x≡z ¬y≡z a b c (swap-z .a .b a≡z aRb yPb) (swap-z .b .c b≡z bRc yPc) = swap-z a c a≡z (R-trans head a b c aRb bRc) yPc
    
    R'-complete : {_R_ : Fin n → Fin n → Set} 
                → (head : Preference n n>1 _R_)
                → (x y z : Fin n)
                → (¬x≡z : ¬ x ≡ z) 
                → (¬y≡z : ¬ y ≡ z)
                → (a b : Fin n)
                → R' head x y z ¬x≡z ¬y≡z a b ⊎ R' head x y z ¬x≡z ¬y≡z b a
    R'-complete head x y z ¬x≡z ¬y≡z a b with a Fin.≟ z | a Fin.≟ y | b Fin.≟ z | b Fin.≟ y | R-complete head a b 
    ... | false because ofⁿ ¬a≡z | _ | _ | false because ofⁿ ¬b≡y | inj₁ aRb = inj₁ (original a b ¬a≡z ¬b≡y aRb)
    ... | _ | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | _ | inj₂ bRa = inj₂ (original b a ¬b≡z ¬a≡y bRa)
    ... | _ | true because ofʸ a≡y | true because ofʸ b≡z | _ | _ = inj₁ (y>z a b a≡y b≡z)
    ... | true because ofʸ a≡z | _ | _ | true because ofʸ b≡y | _ = inj₂ (y>z b a b≡y a≡z)
    ... | true because ofʸ a≡z | ay | bz | false because ofⁿ ¬b≡y | rcom = {! bz  !}
    ... | false because ofⁿ ¬a≡z | false because ofⁿ ¬a≡y | true because ofʸ b≡z | false because ofⁿ ¬b≡y | inj₂ bRa = {!   !}
    ... | false because ofⁿ ¬a≡z | true because ofʸ a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬b≡y | inj₂ bRa = {!   !}
    ... | false because ofⁿ ¬a≡z | ay | bz | true because ofʸ b≡y | rcom = {!   !}
    
    R'-dec : {_R_ : Fin n → Fin n → Set} 
           → (head : Preference n n>1 _R_)
           → (x y z : Fin n)
           → (¬x≡z : ¬ x ≡ z) 
           → (¬y≡z : ¬ y ≡ z)
           → (a b : Fin n)
           → R' head x y z ¬x≡z ¬y≡z a b ⊎ ¬ R' head x y z ¬x≡z ¬y≡z a b
    R'-dec head x y z ¬x≡z ¬y≡z a b = {!   !} {- with a Fin.≟ y | b Fin.≟ z
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
       → (x y z : Fin n)
       → (¬x≡z : ¬ x ≡ z) 
       → (¬y≡z : ¬ y ≡ z)
       → Preference n n>1 (R' head x y z ¬x≡z ¬y≡z)
    P' head x y z ¬x≡z ¬y≡z = record { R-trans    = R'-trans    head x y z ¬x≡z ¬y≡z 
                                     ; R-complete = R'-complete head x y z ¬x≡z ¬y≡z 
                                     ; R-dec      = R'-dec      head x y z ¬x≡z ¬y≡z }
    
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