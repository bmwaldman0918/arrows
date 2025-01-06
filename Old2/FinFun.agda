module FinFun where

open import Data.Nat as ℕ hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool as Bool hiding (_≟_)
open import Relation.Unary as U using (Pred; ∁; _⊆_; _∈_)
open import Relation.Binary as B 
open import Data.Fin as Fin hiding (splitAt; _≟_)
open import Data.Fin.Properties as FinProp hiding (all?; eq?; _≟_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; cong-app)

private 
  variable
    n : ℕ

Voter : ℕ → Set
Voter n = Fin n → Fin n → Bool

postulate extensionality : ∀ {A : Set} 
                             {B : A → Set} 
                             {f g : ∀ (x : A) → B x}
                         → (∀ (x : A) → (f x ≡ g x)) 
                         → f ≡ g

fin→bool-same? : (f g : Fin n → Bool) 
      → (x : Fin n)
      → Dec (f x ≡ g x)
fin→bool-same? f g x = Bool._≟_ (f x) (g x)

fin→bool-eq? : (f g : Fin n → Bool) 
      → Dec (∀ (x : Fin n) → f x ≡ g x)
fin→bool-eq? f g = FinProp.all? (fin→bool-same? f g) 

voter-same? : (f g : Voter n) 
      → (x : Fin n)
      → Dec (f x ≡ g x)
voter-same? f g x with fin→bool-eq? (f x) (g x) 
... | false because ofⁿ ¬p = false because (ofⁿ (λ fx≡gx → ¬p (λ y → cong-app fx≡gx y)))
... | true because ofʸ p = true because (ofʸ (extensionality p))

voter-eq? : (f g : Voter n) 
      → Dec (∀ (x : Fin n) → f x ≡ g x)
voter-eq? f g = FinProp.all? (voter-same? f g)

_≟_ : Decidable {A = Voter n} _≡_
_≟_ f g with voter-eq? f g 
... | false because ofⁿ ¬p = false because ofⁿ λ f≡g → ¬p (λ x → cong-app f≡g x)
... | true because ofʸ p = true because ofʸ (extensionality p) 