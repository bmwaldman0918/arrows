module VecUtil where

open import Relation.Unary using (Pred; ∁; Decidable)
open import Data.Vec using (_∷_; Vec)
open import Data.Vec.Relation.Unary.All using (All; []; all?; uncons)
open import Data.Vec.Relation.Unary.Any using (Any; any?; here; there; satisfied; toSum)
open import Level using (Level)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false)
open import Data.Nat as ℕ using (ℕ; _>_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
    variable
        m : ℕ
        m>0 : m ℕ.> 0

AnyP→¬AllCP : ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → Any P xs → ¬ All (∁ P) xs
AnyP→¬AllCP (here px) (cpx All.∷ _) = cpx px 
AnyP→¬AllCP (there any-P) (_ All.∷ all-C-P) = AnyP→¬AllCP any-P all-C-P

AnyCP→¬AllP : ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → Any (∁ P) xs → ¬ All P xs
AnyCP→¬AllP (here px) (px' All.∷ _) = px px'
AnyCP→¬AllP (there p) (_ All.∷ p') = AnyCP→¬AllP p p'

AllP→¬AnyCP : ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → All P xs → ¬ Any (∁ P) xs
AllP→¬AnyCP (px All.∷ _) (here px') = px' px
AllP→¬AnyCP (_ All.∷ p) (there p') = AllP→¬AnyCP p p'

AllCP→¬AnyP : ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → All (∁ P) xs → ¬ Any P xs
AllCP→¬AnyP (px All.∷ _) (here px') = px px'
AllCP→¬AnyP (_ All.∷ p) (there p') = AllCP→¬AnyP p p'

¬AnyP→AnyCP : {m>0 : m > 0} → ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → (Decidable P) → ¬ Any P xs → Any (∁ P) xs
¬AnyP→AnyCP {P = P} {xs = head ∷ tail} dec ¬AnyP with dec head 
... | false because ofⁿ ¬p-head = here ¬p-head
... | true because ofʸ p-head = ⊥-elim (¬AnyP (here p-head))

¬AllP→AnyCP : {m>0 : m > 0} → ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → (Decidable P) → ¬ All P xs → Any (∁ P) xs
¬AllP→AnyCP {P = P} {xs = head ∷ tail} dec ¬AllP with dec head | all? dec tail
¬AllP→AnyCP {P = P} {head ∷ _} dec ¬AllP | false because ofⁿ ¬p-head | _ = here ¬p-head
¬AllP→AnyCP {P = P} {head ∷ Vec.[]} dec ¬AllP | true because ofʸ p | _ = ⊥-elim (¬AllP (p All.∷ []))
¬AllP→AnyCP {P = P} {head ∷ _∷_ {ℕ.zero} x Vec.[]} dec ¬AllP | true because ofʸ p-head | false because ofⁿ ¬p-tail with dec x 
... | false because ofⁿ ¬px = there (here ¬px)
... | true because ofʸ px = ⊥-elim (¬p-tail (px All.∷ []))
¬AllP→AnyCP {P = P} {head ∷ _∷_ {ℕ.suc n} x tail} dec ¬AllP | true because ofʸ p-head | false because ofⁿ ¬p-tail = there (¬AllP→AnyCP {m>0 = ℕ.s≤s ℕ.z≤n} dec ¬p-tail)
¬AllP→AnyCP {P = P} {head ∷ _∷_ {n} x tail} dec ¬AllP | true because ofʸ p-head | true because ofʸ all-p-tail = ⊥-elim (¬AllP (p-head All.∷ all-p-tail))

¬AnyP→AllCP : ∀ {a b} → {A : Set a} → {P : Pred A b} → {xs : Vec A m} → (Decidable P) → ¬ Any P xs → All (∁ P) xs
¬AnyP→AllCP {P = P} {xs = Vec.[]} _ _             = [] 
¬AnyP→AllCP {P = P} {xs = head ∷ tail} dec ¬AnyP with dec head | any? dec tail
¬AnyP→AllCP {P = P} {head ∷ Vec.[]} dec ¬AnyP | false because ofⁿ ¬p-head | false because ofⁿ ¬p-tail = ¬p-head All.∷ []
¬AnyP→AllCP {P = P} {head ∷ _∷_ {n} x tail} dec ¬AnyP | false because ofⁿ ¬p-head | false because ofⁿ ¬p-tail = ¬p-head All.∷ ¬AnyP→AllCP dec ¬p-tail
... | _ | true because ofʸ px = ⊥-elim (¬AnyP (there px))
... | true because ofʸ p | _ = ⊥-elim (¬AnyP (here p))
