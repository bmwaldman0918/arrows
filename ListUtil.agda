module ListUtil where

open import Relation.Unary using (Pred; ∁; Decidable)
open import Data.List using (_∷_; List)
open import Data.List.Relation.Unary.All using (All; []; all?; uncons)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; satisfied; lookup; toSum)
open import Data.List.NonEmpty.Base using (List⁺; toList; _∷_)
open import Level using (Level)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false)

AnyP→¬AllCP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List A} → Any P xs → ¬ All (∁ P) xs
AnyP→¬AllCP (here px) (cpx All.∷ _) = cpx px 
AnyP→¬AllCP (there any-P) (_ All.∷ all-C-P) = AnyP→¬AllCP any-P all-C-P

AnyCP→¬AllP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List A} → Any (∁ P) xs → ¬ All P xs
AnyCP→¬AllP (here px) (px' All.∷ _) = px px'
AnyCP→¬AllP (there p) (_ All.∷ p') = AnyCP→¬AllP p p'

AllP→¬AnyCP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List A} → All P xs → ¬ Any (∁ P) xs
AllP→¬AnyCP (px All.∷ _) (here px') = px' px
AllP→¬AnyCP (_ All.∷ p) (there p') = AllP→¬AnyCP p p'

AllCP→¬AnyP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List A} → All (∁ P) xs → ¬ Any P xs
AllCP→¬AnyP (px All.∷ _) (here px') = px px'
AllCP→¬AnyP (_ All.∷ p) (there p') = AllCP→¬AnyP p p'

¬AnyP→AnyCP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List⁺ A} → (Decidable P) → ¬ Any P (toList xs) → Any (∁ P) (toList xs)
¬AnyP→AnyCP {P = P} {xs = head ∷ tail} dec ¬AnyP with dec head 
... | false because ofⁿ ¬p-head = here ¬p-head
... | true because ofʸ p-head = ⊥-elim (¬AnyP (here p-head))

¬AllP→AnyCP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List⁺ A} → (Decidable P) → ¬ All P (toList xs) → Any (∁ P) (toList xs)
¬AllP→AnyCP {P = P} {xs = head ∷ tail} dec ¬AllP with dec head 
...                                             | false because ofⁿ ¬p-head                           = here ¬p-head 
...                                             | true because ofʸ p-head with all? dec tail 
¬AllP→AnyCP {P = P} {head ∷ List.[]} dec ¬AllP  | true because ofʸ p-head | false because ofⁿ ¬p-tail = ⊥-elim (¬AllP (p-head All.∷ []))
¬AllP→AnyCP {P = P} {head ∷ x ∷ tail} dec ¬AllP | true because ofʸ p-head | false because ofⁿ ¬p-tail = there (¬AllP→AnyCP dec ¬p-tail)
...                                             | true because ofʸ p-tail                             = ⊥-elim (¬AllP (p-head All.∷ p-tail)) 

¬AnyP→AllCP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List A} → (Decidable P) → ¬ Any P xs → All (∁ P) xs
¬AnyP→AllCP {P = P} {xs = List.[]} _ _             = [] 
¬AnyP→AllCP {P = P} {xs = x ∷ xs} dec ¬AnyP with dec x | any? dec xs 
... | false because ofⁿ ¬p | false because ofⁿ ¬px = ¬p All.∷ (¬AnyP→AllCP dec λ anyCPxs → ¬px anyCPxs)
... | false because ofⁿ ¬p | true because ofʸ px   = ⊥-elim (¬AnyP (there px))  
... | true because ofʸ p   | _                     = ⊥-elim (¬AnyP (here p)) 