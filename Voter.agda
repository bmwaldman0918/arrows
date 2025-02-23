module Voter where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec
open import Data.Vec.Relation.Unary.All as All using (All)
open import Relation.Unary using (Pred; ∁; _⊆_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false; Bool)
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)

private
    variable
        n : ℕ
        n>1 : n ℕ.> 1
        a b c : Fin n
        _R_ : Fin n → Fin n → Set

module WeakPreference where
    --- A weak preference is transitive, complete, and decidable relation
    --- A weak preference is not anti-symmetric, so voters can be indifferent between candidates
    record Preference (n : ℕ) (n>1 : n ℕ.> 1) (_R_ : Fin n → Fin n → Set) : Set where
        field
            R-trans    : (a b c : Fin n) → a R b → b R c → a R c
            R-complete : (a b : Fin n)   → (a R b) ⊎   (b R a)
            R-dec      : (a b : Fin n)   → (a R b) ⊎ ¬ (a R b)
    open Preference

    --- Weak preferences are reflexive
    R-refl : (v : Preference n n>1 _R_) 
        → (a b : Fin n)
        → (a ≡ b) 
        ----------------------
        → a R b
    R-refl v a b a≡b with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa rewrite a≡b = bRa

    ¬R-dec→⊥ : {p : Preference n n>1 _R_} → {a b : Fin n} → ¬ (a R b) → ¬ (b R a) → ⊥
    ¬R-dec→⊥ {p = p} {a = a} {b = b} ¬aRb ¬bRa with R-complete p a b 
    ... | inj₁ aRb = ¬aRb aRb
    ... | inj₂ bRa = ¬bRa bRa

    R→Bool : (p : Preference n n>1 _R_) → (a b : Fin n) → Bool
    R→Bool p a b with R-dec p a b 
    ... | inj₁ x = true
    ... | inj₂ y = false
     
open WeakPreference
open Preference

module StrictPreference where
    --- Strict preferences are the absence of the inverted weak preference
    P : (Preference n n>1 _R_) 
        → (a b : Fin n) 
        ----------------------
        → Set
    P {_R_ = _R_} _ a b = ¬ (b R a)

    --- Strict preferences imply weak preferences
    P→R : {a b : Fin n} 
        → {v : Preference n n>1 _R_} 
        → (P v a b) 
        --------------------------
        → a R b
    P→R {a = a} {b = b} {v = v} ¬bRa with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa = ⊥-elim (¬bRa bRa)

    --- Strict preferences imply inequality
    P↛≡ : {v : Preference n n>1 _R_} 
        → (P v a b) 
        --------------------------
        → ¬ (a ≡ b)
    P↛≡ {a = a} {b = b} {v = v} ¬bRb a≡b = ¬bRb (R-refl v b a (Eq.sym a≡b))

    --- Strict preference is transitive
    P-trans : {v : Preference n n>1 _R_} 
            → P v a b 
            → P v b c 
            --------------------------
            → P v a c
    P-trans {a = a} {b = b} {c = c} {v = v} 
        with (R-dec v a b) | (R-complete v a b) 
    ...      | inj₁ aRb    | _                 = λ  bRc ¬cRb cRa → ¬cRb (R-trans v c a b cRa aRb)
    ...      | inj₂ ¬aRb   | inj₁ aRb          = λ ¬bRa ¬cRb cRa → ⊥-elim (¬aRb aRb)
    ...      | _           | inj₂ bRa          = λ ¬bRa ¬cRb cRa → ⊥-elim (¬bRa bRa)

    P→Bool : (p : Preference n n>1 _R_) → (a b : Fin n) → Bool
    P→Bool p a b with R-dec p b a 
    ... | inj₁ x = false
    ... | inj₂ y = true
open StrictPreference

module PreferenceEquality where
  ≡-Preference : {_R_ _R'_ : Fin n → Fin n → Set}
               → Preference n n>1 _R_
               → Preference n n>1 _R'_
               → Set
  ≡-Preference p p' = ∀ x y → R→Bool p x y ≡ R→Bool p' x y
  