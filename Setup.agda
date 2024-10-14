open import Data.Sum using (_⊎_)
open import Data.List.NonEmpty.Base using (List⁺; toList)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Level using (0ℓ; Level; suc)
open import Relation.Nullary using (¬_; Dec)
open import Data.Empty
open import Data.Bool using (true; false)

module Setup where

1L : Level
1L = suc 0ℓ

2L : Level
2L = suc 1L

private
    postulate
        Candidate : Set
        a b c : Candidate

record Preference (_R_ : Candidate → Candidate → Set) : Set₁ where
    field
        R-refl : (a : Candidate) → a R a
        R-trans : a R b → b R c → a R c
        R-complete : (a b : Candidate) → (a R b) ⊎ (b R a)
        R-dec : (a b : Candidate) → (a R b) ⊎ ¬ (a R b)
open Preference

private
    variable
        _R_ : Candidate → Candidate → Set

data P  : (Preference _R_) → (a b : Candidate) → Set₁ where
    P-gen : (election : Preference _R_) → (a b : Candidate) → ¬ (b R a) → P election a b

P-trans : {e : Preference _R_} → P e a b → P e b c → P e a c
P-trans {_R_} {election} (P-gen election _ _ ¬bRa) (P-gen election _ _ ¬cRb) with (R-dec election a b) 
                                        | (R-complete election a b) 
                                        | (R-dec election b c) 
                                        | (R-complete election b c)
... | _⊎_.inj₁ _ | _⊎_.inj₁ aRb | _⊎_.inj₁ _ | _⊎_.inj₁ bRc = 
    P-gen election a c λ cRa → ¬cRb (R-trans {! election  !} {!   !} {!   !})
... | _⊎_.inj₁ aRb | _⊎_.inj₁ _ | _⊎_.inj₁ bRc | _⊎_.inj₂ cRb = ⊥-elim (¬cRb cRb)
... | _⊎_.inj₁ aRb | _⊎_.inj₁ _ | _⊎_.inj₂ ¬bRc | _⊎_.inj₁ bRc = ⊥-elim (¬bRc bRc)
... | _⊎_.inj₁ aRb | _⊎_.inj₁ _ | _⊎_.inj₂ y | _⊎_.inj₂ cRb = ⊥-elim (¬cRb cRb)
... | _⊎_.inj₁ aRb | _⊎_.inj₂ bRa | _ | _ = ⊥-elim (¬bRa bRa)
... | _⊎_.inj₂ ¬aRb | _⊎_.inj₁ aRb | _ | _ = ⊥-elim (¬aRb aRb)
... | _⊎_.inj₂ ¬aRb | _⊎_.inj₂ bRa | _ | _ = ⊥-elim (¬bRa bRa)
{-
        P-gen : (a b : Candidate) → ¬ (b R a) → a P b
        P-trans : {a b c : Candidate} → a P b → b P c → a P c
        P→R : {a b : Candidate} → (a P b) → a R b
        P↛≡ : {a b : Candidate} → (a P b) → ¬ (a ≡ b)


Voter : Set₁
Voter = Preference

dec-prefers : (a b : Candidate) → (v : Voter) → Set
dec-prefers a b v = Dec (Preference._P_ v a b)

prefers? : (a b : Candidate) → (v : Voter) → (dec-prefers a b v)
prefers? a b v with Preference.R-dec v a b 
... | _⊎_.inj₁ x = true Relation.Nullary.because Relation.Nullary.ofʸ {!   !}
... | _⊎_.inj₂ y = false Relation.Nullary.because Relation.Nullary.ofⁿ {!   !} 

prefers : (a b : Candidate) → Pred Preference 0ℓ
prefers a b v = Preference._P_ v a b

record socialPreference : Set₁ where
    field
        ballots : List⁺ (Voter)
        socialPreferenceFunction : Preference 
        unanimity : (a b : Candidate) → All (prefers a b) (toList ballots) → (prefers a b socialPreferenceFunction)

decisive : (a b : Candidate) → (socialPreference) → (v : Voter) → Set
decisive a b sp v = Preference._P_ v a b → Preference._P_ (socialPreference.socialPreferenceFunction sp) a b

dictator : (socialPreference) → (v : Voter) → Set 
dictator sp v = ∀ (x y : Candidate) → decisive x y sp v
-}  