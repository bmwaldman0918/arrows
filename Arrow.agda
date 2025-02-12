module Arrow where

open import Voter
open WeakPreference using (Preference)
open import Votes 
open import Election
open import Coalition
open import Decisive
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
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
                                    × ElectionAgrees v' x z)
LemmaTwoSimilar zero [] [] x y z ¬x≡z ¬y≡z _ _ _ = [] , (tt , tt)
LemmaTwoSimilar (suc m) (false ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (false-agrees .c .rem ca-x>y .head) 
                (true-agrees .(InverseCoalition c) .rem in-ca-y>x .head x₁)
                (false-agrees .c .rem ca-x>z .head) 
    with LemmaTwoSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z
... | sim-coal , is-sim , sim-x>z = (P' ∷ sim-coal) , ({!   !} , is-sim) , ({!   !} , sim-x>z)
    where 
    _R'_ : Fin n → Fin n → Set
    _R'_ a b = {!   !}
    P' : Preference n n>1 _R'_
    P' = {!   !}
LemmaTwoSimilar (suc m) (true ∷ c) (head ∷ rem) x y z ¬x≡z ¬y≡z 
                (true-agrees .c .rem ca-x>y .head x₁) 
                (false-agrees .(InverseCoalition c) .rem in-ca-y>x .head)
                (true-agrees .c .rem ca-x>z .head x₂)
    with LemmaTwoSimilar m c rem x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z
... | sim-coal , is-sim , sim-x>z = (P' ∷ sim-coal) , ({!   !} , is-sim) , ({!   !} , sim-x>z)
    where 
    _R'_ : Fin n → Fin n → Set
    _R'_ a b = {!   !}
    P' : Preference n n>1 _R'_
    P' = {!   !}

LemmaTwo : (m : ℕ) → (c : Coalition m) → (v : Votes n n>1 m) → (x y z : Fin n) → ¬ (x ≡ z) → ¬ (y ≡ z) → Decisive-a>b c v x y → StrictlyDecisive-a>b c v x z 
LemmaTwo m c v x y z ¬x≡z ¬y≡z (dec-a>b ca-x>y in-ca-y>x _) ca-x>z with LemmaTwoSimilar m c v x y z ¬x≡z ¬y≡z ca-x>y in-ca-y>x ca-x>z
... | sim-coal , is-sim , sim-x>z = BinaryIIA x z sim-coal is-sim (Pareto x z sim-x>z)