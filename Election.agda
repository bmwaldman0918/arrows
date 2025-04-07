module Election where

open import Voter
open WeakPreference using (Preference)
open import Votes

open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Vec as Vec
open import Data.Bool as Bool
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Unit

private
    variable
        m n : ℕ
        n>2 : n ℕ.> 2
        a b c : Fin n
        Result : Fin n → Fin n → Set

-- SWF v a b represents a strict preference for a over b given a set of votes v
-- SWF : {m n : ℕ} → {n>2 : n ℕ.> 2} → (v : Votes n n>2 m) → Set₁
-- SWF {n = n} v = Fin n → Fin n → Set

-- since an SWF (or social welfare function) represents a strict preference,
-- we postulate that it is decidable and transitive but not complete

record SWF {n : ℕ} {n>2 : n ℕ.> 2} 
  (Result : {m : ℕ} → Votes n n>2 m → Fin n → Fin n → Set) : Set₁ where
  field
    -- arrow's specific postulates
    Pareto      : {m : ℕ} 
                → (v : Votes n n>2 m) 
                → (a b : Fin n)   
                → ElectionAgrees v a b 
                → Result v a b 
    BinaryIIA   : {m : ℕ} 
                → (v v' : Votes n n>2 m)
                → (a b : Fin n)
                → Similar m a b (Zipped n>2 a b v v')
                → Result v' a b
                → Result v a b

    -- properties of the swf relation
    Transitive  : {m : ℕ} 
                → (v : Votes n n>2 m) 
                → (a b c : Fin n) 
                → Result v a b 
                → Result v b c 
                → Result v a c

    Decidable   : {m : ℕ} 
                → (v : Votes n n>2 m) 
                → (a b : Fin n)   
                →   (Result v a b) 
                ⊎ ¬ (Result v a b)

    Asymmetric  : {m : ℕ} 
                → (v : Votes n n>2 m) 
                → (a b : Fin n)
                → Result v a b
                → ¬ Result v b a