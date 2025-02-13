module Arrow where

open import Voter
open WeakPreference
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
open import Data.Sum using (_⊎_)
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
LemmaTwoAlter head x y z ¬x≡z ¬y≡z = R' head x y z , P' head x y z , {!   !} , {!   !} , {!   !}
  where
  R' : {_R_ : Fin n → Fin n → Set} 
     → (head : Preference n n>1 _R_)
     → (x y z : Fin n) 
     → (Fin n → Fin n → Set)
  R' {_R_ = _R_} head x y z a b with a Fin.≟ z | b Fin.≟ y
  ... | true because ofʸ a≡z | true because ofʸ b≡y = ⊥
  ... | _ | _ with a Fin.≟ y | b Fin.≟ z
  ... | true because ofʸ a≡z | true because ofʸ b≡y = ⊤
  ... | _ | _ = a R b

  P' : {_R_ : Fin n → Fin n → Set} 
     → (head : Preference n n>1 _R_)
     → (x y z : Fin n) 
     → Preference n n>1 (R' head x y z)
  P' head x y z = {!   !}

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