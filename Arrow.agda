module Arrow where

open import Voter
open import Votes
open import Election
open import Coalition
open import Decisive
open import Data.Nat as ℕ
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (inspect)

private
  variable
    m n : ℕ
    n>1 : n ℕ.> 1

-- the coalition of the whole is decisive

PredCoalitionOfWhole : (m : ℕ) → (v : Votes n n>1 (suc m)) → (a b : Fin n) → CoalitionAgrees v a b (proj₁ (CoalitionOfWhole (suc m))) → CoalitionAgrees (PredVotes m v) a b (proj₁ (CoalitionOfWhole m))
PredCoalitionOfWhole = {!   !}

LemmaOne : (m : ℕ) → (v : Votes n n>1 m) → (a b : Fin n) → CoalitionAgrees v a b (proj₁ (CoalitionOfWhole m)) → ElectionAgrees v a b
LemmaOne .0 [] a b ca = λ idx → λ ()
LemmaOne .(suc _) (x ∷ v) a b (cons-coalition-agrees .(Lift (proj₁ (CoalitionOfWhole _))) _ _ x₁ ca) = {!   !}