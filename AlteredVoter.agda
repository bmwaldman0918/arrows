module AlteredVoter where
  
open import Data.Nat as ℕ hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool as Bool hiding (_≟_)
open import Data.Bool.Properties as BoolProp hiding (_≟_)
open import Data.List as List
open import Data.Vec as Vec
open import Data.Vec.Relation.Unary.Any as VecAny
open import Data.List.Relation.Unary.Any as ListAny
open import Data.List.Relation.Unary.All as ListAll
open import Data.Vec.Relation.Unary.All as VecAll
open import Relation.Unary as U using (Pred; ∁; _⊆_; _∈_)
open import Relation.Binary as B 
open import Data.Fin as Fin hiding (splitAt; _≟_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import FinFun

private
    variable
        m n : ℕ --- numbers of ballots/number of candidates
        m>0 : m ℕ.> 0 --- at least ballot
        n>1 : n ℕ.> 1 --- at least two candidates
        x y z : Fin n
        y≠z : ¬(y ≡ z)
        x≠z : ¬(x ≡ z)
        x≠y : ¬(x ≡ y)
        all-ballots altered-ballots : Vec (Voter n) m
        G : List (Voter n)

Alter-Voter-For-FieldExpansion : Fin n → Fin n → Fin n → Voter n → List (Voter n) → Voter n
Alter-Voter-For-FieldExpansion x y z v G a b with a Fin.≟ y | b Fin.≟ z 
... | true because ofʸ a≡y | true because ofʸ b≡z = true
... | a≟y | b≟z with ListAny.any? (_≟_ v) G 
... | false because ofⁿ ¬v∈G with a Fin.≟ x | b Fin.≟ y
... | true because ofʸ a≡x | true because ofʸ b≡y = true
... | a≟x | b≟y = v a b
Alter-Voter-For-FieldExpansion x y z v G a b | a≟y | b≟z | true because ofʸ v∈G with a Fin.≟ y | b Fin.≟ x 
... | true because ofʸ a≡y | true because ofʸ b≡x = true
... | a≟y | b≟x = v a b

Altered-Voter-exy≡true : (x y z : Fin n)
                      → ¬ x ≡ y
                      → ¬ y ≡ z
                      → ¬ x ≡ z
                      → (v : Voter n)
                      → Alter-Voter-For-FieldExpansion x y z v G x y ≡ true
Altered-Voter-exy≡true {G = G} x y z ¬x≡y ¬y≡z ¬x≡z v with x Fin.≟ y | y Fin.≟ z
... | true because ofʸ x≡y | y≟z = ⊥-elim (¬x≡y x≡y)
... | x≟y | true because ofʸ y≡z = ⊥-elim (¬y≡z y≡z)
... | false because ofⁿ ¬x≡y | false because ofⁿ ¬y≡z with ListAny.any? (_≟_ v) G 
... | false because ofⁿ ¬v∈G with x Fin.≟ x | y Fin.≟ y 
... | false because ofⁿ ¬x≡x | y≟y = ⊥-elim (¬x≡x Eq.refl)
... | true because ofʸ x≡x | false because ofⁿ ¬y≡y = ⊥-elim (¬y≡y Eq.refl)
... | true because ofʸ x≡x | true because ofʸ y≡y = Eq.refl
Altered-Voter-exy≡true {G = G} x y z _ _ ¬x≡z v | false because ofⁿ ¬x≡y | false because ofⁿ ¬y≡z | true because ofʸ v∈G with x Fin.≟ y | y Fin.≟ x 
... | true because ofʸ x≡y | y≟x = ⊥-elim (¬x≡y x≡y)
... | false because ofⁿ ¬x≡y | y≟x = {!   !}

Similar-Voter : (x y z : Fin n)
                → ¬ x ≡ y
                → ¬ y ≡ z
                → ¬ x ≡ z
                → (v : Voter n)
                → v x z ≡ Alter-Voter-For-FieldExpansion x y z v G x z
Similar-Voter {G = G} x y z x≠y y≠z x≠z v with x Fin.≟ y | z Fin.≟ z
... | true because ofʸ x≡y | z≟z = ⊥-elim (x≠y x≡y)
... | x≟y | false because ofⁿ ¬z≡z = ⊥-elim (¬z≡z Eq.refl) 
... | false because ofⁿ ¬x≡y | true because ofʸ z≡z with ListAny.any? (_≟_ v) G
... | false because ofⁿ ¬v∈G with x Fin.≟ x | z Fin.≟ y
... | false because ofⁿ ¬x≡x | z≟y = ⊥-elim (¬x≡x Eq.refl)
... | true because ofʸ x≡x | false because ofⁿ ¬z≡y = Eq.refl
... | true because ofʸ x≡x | true because ofʸ z≡y = ⊥-elim (y≠z (Eq.sym z≡y))   
Similar-Voter {G = G} x y z x≠y y≠z x≠z v | false because ofⁿ ¬x≡y | true because ofʸ z≡z | true because ofʸ v∈G with x Fin.≟ y | z Fin.≟ x
... | false because ofⁿ ¬x≡y | z≟x = Eq.refl 
... | true because ofʸ x≡y | false because ofⁿ ¬z≡x = ⊥-elim (x≠y x≡y)       
... | true because ofʸ x≡y | true because ofʸ z≡x = ⊥-elim (x≠z (Eq.sym z≡x))