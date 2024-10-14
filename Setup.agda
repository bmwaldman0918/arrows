open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Level using (0ℓ; Level; suc)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false)

module Setup where

1L : Level
1L = suc 0ℓ

2L : Level
2L = suc 1L

private
    variable
        Candidate : Set


--- weak preference

record Preference (_R_ : Candidate → Candidate → Set) : Set₁ where
    field
        R-refl : (a : Candidate) → a R a
        R-trans : {a b c : Candidate} → a R b → b R c → a R c
        R-complete : (a b : Candidate) → (a R b) ⊎ (b R a)
        R-dec : (a b : Candidate) → (a R b) ⊎ ¬ (a R b)
open Preference

--- definitions and properties of strict preference 

data P : {_R_ : Candidate → Candidate → Set} → (Preference _R_) → (a b : Candidate) → Set₁ where
    P-gen : {_R_ : Candidate → Candidate → Set} → 
            (election : Preference _R_) → 
            (a b : Candidate) → ¬ (b R a) → P election a b

P→R : {_R_ : Candidate → Candidate → Set} → {a b : Candidate} → {v : Preference _R_} → 
        (P v a b) → a R b
P→R (P-gen v a b ¬bRa) with R-dec v a b | R-complete v a b
... | inj₁ aRb  | _        = aRb
... | _         | inj₁ aRb = aRb
... | _         | inj₂ bRa = ⊥-elim (¬bRa bRa)

P↛≡ : {_R_ : Candidate → Candidate → Set} → {a b : Candidate} → (v : Preference _R_) → 
        (P v a b) → ¬ (a ≡ b)
P↛≡ v (P-gen _ a b ¬bRa) a≡b rewrite a≡b = ¬bRa (R-refl v b)

P→¬R : {_R_ : Candidate → Candidate → Set} → {a b : Candidate} → {v : Preference _R_} → 
        (P v a b) → ¬ (b R a)
P→¬R (P-gen _ _ _ ¬bRa) = ¬bRa

P-trans : {_R_ : Candidate → Candidate → Set} → {a b c : Candidate} → {v : Preference _R_} → 
            P v a b → P v b c → P v a c
P-trans (P-gen election a b ¬bRa) (P-gen election b c ¬cRb) with (R-dec election a b) 
                                        | (R-complete election a b) 
                                        | (R-dec election b c) 
                                        | (R-complete election b c)
... | inj₁ _ | inj₁ aRb | inj₁ _ | inj₁ bRc = 
            P-gen election a c λ cRa → ¬cRb (R-trans election cRa aRb)

... | inj₂ ¬aRb | inj₁ aRb | _          | _        = ⊥-elim (¬aRb aRb)
... | _         | inj₂ bRa | _          | _        = ⊥-elim (¬bRa bRa)
... | _         | _        | inj₂ ¬bRc  | inj₁ bRc = ⊥-elim (¬bRc bRc)
... | _         | _        | _          | inj₂ cRb = ⊥-elim (¬cRb cRb)

--- functions related to voter preference
Voter : (R : Candidate → Candidate → Set) → Set₁ 
Voter R = Preference R

dec-prefers : {_R_ : Candidate → Candidate → Set} → (a b : Candidate) → (v : Voter _R_) → Set₁ 
dec-prefers a b v = Dec (P v a b)

prefers? : {_R_ : Candidate → Candidate → Set} → (a b : Candidate) → (v : Voter _R_) → 
        (dec-prefers a b v)
prefers? a b v with Preference.R-dec v b a | Preference.R-dec v a b | R-complete v a b
... | inj₁ bRa | inj₁ aRb | _ = false because ofⁿ (λ aPb → P→¬R aPb bRa)
... | inj₁ bRa | inj₂ ¬aRb | _ = false because ofⁿ (λ aPb → P→¬R aPb bRa)
... | inj₂ ¬bRa | inj₁ aRb | _ = true because (ofʸ (P-gen v a b ¬bRa))
... | inj₂ ¬bRa | inj₂ ¬aRb | inj₁ aRb = ⊥-elim (¬aRb aRb)
... | inj₂ ¬bRa | inj₂ ¬aRb | inj₂ bRa = ⊥-elim (¬bRa bRa)


--- curried version of P for convenience
prefers : {_R_ : Candidate → Candidate → Set} → (a b : Candidate) → (v : Voter _R_) → Set₁
prefers a b v = P v a b

record socialPreference (_R_ : Candidate → Candidate → Set) : Set₁ where
    field

        ballots : List⁺ (Voter _R_)
        socialPreferenceFunction : Preference _R_
        unanimity : (a b : Candidate) → All (prefers a b) (toList ballots) → (prefers a b socialPreferenceFunction)
open socialPreference

decisive : {_vR_ _spR_ : Candidate → Candidate → Set} → 
            (a b : Candidate) → (socialPreference _spR_ ) → (v : Voter _vR_) → Set₁
decisive a b sp v = P v a b → P (socialPreferenceFunction sp) a b
 
dictator : {candidate : Set} → {_vR_ _spR_ : candidate → candidate → Set} → 
        (socialPreference _spR_) → (v : Voter _vR_) → Set₁
dictator {candidate} sp v = ∀ (a b : candidate) → decisive a b sp v