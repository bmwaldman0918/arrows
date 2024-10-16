module ListUtil where

open import Relation.Unary using (Pred; ∁)
open import Data.List using (_∷_; List)
open import Data.List.Relation.Unary.All using (All; []; all?; uncons)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; satisfied)
open import Level using (Level)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty

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

{-
¬AllP→AnyCP : {a : Level} → {A : Set a} → {P : Pred A a} → {xs : List A} →  ¬ All P xs → Any (∁ P) xs
¬AllP→AnyCP {xs = List.[]} p = ⊥-elim (p []) 
¬AllP→AnyCP {P = P} {xs = x ∷ xs} ¬AllP = {!   !}
-}