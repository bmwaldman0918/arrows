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
open import Relation.Nullary.Decidable using (isYes)
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
Alter-Voter-For-FieldExpansion x y z v G a b with a Fin.≟ y | b Fin.≟ z | ListAny.any? (_≟_ v) G | a Fin.≟ x | b Fin.≟ y
... | true because _ | true because _ | _ | _ | _ = true
... | _ | _ | false because _ | true because _ | true because _ = false
... | _ | _ | false because _ | _ | _ = v a b
... | _ | _ | true because _ | true because _ | true because _ = true
... | _ | _ | true because _ | _ | _ = v a b

Altered-Voter : (x y z : Fin n) → (v : Voter n) → (G : List (Voter n)) → (a b : Fin n) → Dec (v a b ≡ Alter-Voter-For-FieldExpansion x y z v G a b)
Altered-Voter x y z v G a b with a Fin.≟ y | b Fin.≟ z | ListAny.any? (_≟_ v) G | a Fin.≟ x | b Fin.≟ y
Altered-Voter x y z v G a b | true because a≡y | true because b≡z | v∈G? | a≟x | b≟y with v a b 
... | false = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl)
... | true = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬v∈G | true because ofʸ a≡x | true because ofʸ b≡y with v a b 
... | false = true because ofʸ Eq.refl
... | true = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl)
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | true because ofʸ b≡z | false because ofⁿ ¬v∈G | true because ofʸ a≡x | true because ofʸ b≡y with v a b 
... | false = true because ofʸ Eq.refl
... | true = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl)
Altered-Voter x y z v G a b | true because ofʸ a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬v∈G | true because ofʸ a≡x | true because ofʸ b≡y with v a b 
... | false = true because ofʸ Eq.refl
... | true = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl)
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬v∈G | false because ofⁿ ¬a≡x | b≟y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬v∈G | true because ofʸ a≡x | false because ofⁿ ¬b≡y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | true because ofʸ b≡z | false because ofⁿ ¬v∈G | false because ofⁿ ¬a≡x | b≟y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | true because ofʸ b≡z | false because ofⁿ ¬v∈G | true because ofʸ a≡x | false because ofⁿ ¬b≡y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | true because ofʸ a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬v∈G | false because ofⁿ ¬a≡x | b≟y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | true because ofʸ a≡y | false because ofⁿ ¬b≡z | false because ofⁿ ¬v∈G | true because ofʸ a≡x | false because ofⁿ ¬b≡y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | true because ofʸ v∈G | false because ofⁿ ¬a≡x | b≟y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | true because ofʸ v∈G | true because ofʸ a≡x | false because ofⁿ ¬b≡y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | false because ofⁿ ¬b≡z | true because ofʸ v∈G | true because ofʸ a≡x | true because ofʸ b≡y with v a b 
... | false = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl) 
... | true = true because ofʸ Eq.refl 
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | true because ofʸ b≡z | true because ofʸ v∈G | false because ofⁿ ¬a≡x | b≟y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | true because ofʸ b≡z | true because ofʸ v∈G | true because ofʸ a≡x | false because ofⁿ ¬b≡y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | false because ofⁿ ¬a≡y | true because ofʸ b≡z | true because ofʸ v∈G | true because ofʸ a≡x | true because ofʸ b≡y with v a b 
... | false = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl) 
... | true = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | true because ofʸ a≡y | false because ofⁿ ¬b≡z | true because ofʸ v∈G | false because ofⁿ ¬a≡x | b≟y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | true because ofʸ a≡y | false because ofⁿ ¬b≡z | true because ofʸ v∈G | true because ofʸ a≡x | false because ofⁿ ¬b≡y = true because ofʸ Eq.refl
Altered-Voter x y z v G a b | true because ofʸ a≡y | false because ofⁿ ¬b≡z | true because ofʸ v∈G | true because ofʸ a≡x | true because ofʸ b≡y with v a b 
... | false = false because ofⁿ (λ f≡t → BoolProp.not-¬ f≡t Eq.refl) 
... | true = true because ofʸ Eq.refl