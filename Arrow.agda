module Arrow where

open import Voter
open WeakPreference using (Preference)
open import Votes 
open import Election
open import Coalition
open import Decisive
open import Data.Nat as ℕ
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (inspect)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Bool
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Properties as ℕProp

private
  variable
    m n : ℕ
    n>1 : n ℕ.> 1
    a b : Fin n
    _R_ : Fin n → Fin n → Set
    v : Preference n n>1 _R_

-- the coalition of the whole is decisive

LemmaOne : (m : ℕ) → (v : Votes n n>1 m) → (a b : Fin n) → CoalitionAgrees v a b (proj₁ (CoalitionOfWhole m)) → ElectionAgrees v a b
LemmaOne zero [] a b ca = tt  
LemmaOne (suc m) (v ∷ rem) a b (cons-coalition-agrees .(Lift (CoalitionOfWhole m .proj₁)) .m .(n<1+n m) x ca) = x , (LemmaOne m rem a b {!   !}) 