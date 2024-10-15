module Setup where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false)
open import Function.Bundles using (_↔_)
   
--- weak preference

record WeakAntiPreference {Candidate : Set} (_R_ : Candidate → Candidate → Set) : Set where
    field
        R-refl : {a : Candidate} → a R a
        R-trans : {a b c : Candidate} → a R b → b R c → a R c
        R-complete : {a b : Candidate} → (a R b) ⊎ (b R a)
        R-dec : {a b : Candidate} → (a R b) ⊎ ¬ (a R b)
open WeakAntiPreference

--- definitions and properties of strict preference 

complement : {Candidate : Set} (_R_ : Candidate → Candidate → Set)
  → Candidate → Candidate → Set
complement _R_ a b = ¬ (b R a)

complement-WeakAntiPreference-is-not-reflexive :
  ∀ {Candidate : Set} {_R_ : Candidate → Candidate → Set}
  → WeakAntiPreference _R_
  → (a : Candidate)
  → ¬ ((complement _R_) a a)
complement-WeakAntiPreference-is-not-reflexive wap_R a not_refl_a 
  with R-refl wap_R
... | z = not_refl_a (z {a})

record Voter {Candidate : Set} : Set₁ where
     field
        r : Candidate → Candidate → Set
        prefs : WeakAntiPreference r
open Voter

prefers : {Candidate : Set} → (a b : Candidate) → (v : Voter {Candidate}) → Set
prefers a b v = complement (r v) a b

record socialPreference {Candidate : Set} : Set₁ where
    field
        ballots : List⁺ (Voter {Candidate})
        socialPreferenceFunction : Voter {Candidate}
        unanimity : (a b : Candidate) 
                → All (prefers a b) (toList ballots) 
                → (prefers a b socialPreferenceFunction)
open socialPreference

decisive : {Candidate : Set} → (a b : Candidate) → (socialPreference {Candidate}) → (v : Voter {Candidate}) → Set
decisive a b sp v = complement (r v) a b →  complement (r (socialPreferenceFunction sp)) a b
 
dictator : {Candidate : Set} → (socialPreference {Candidate}) → (v : Voter {Candidate}) → Set
dictator {candidate} sp v = ∀ (a b : candidate) → decisive a b sp v


{-
        (Preference _R_) → (a b : Candidate) → Set where
    P-gen : {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → 
            (election : Preference _R_) → 
            (a b : Candidate) → ¬ (b R a) → P election a b


P→R : {Candidate : Set} → {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → {a b : Candidate} → 
        {v : Preference _R_} → (P v a b) → a R b
P→R (P-gen v a b ¬bRa) with R-dec v a b | R-complete v a b
... | inj₁ aRb  | _        = aRb
... | _         | inj₁ aRb = aRb
... | _         | inj₂ bRa = ⊥-elim (¬bRa bRa)

P↛≡ : {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → {a b : Candidate} → (v : Preference _R_) → 
        (P v a b) → ¬ (a ≡ b)
P↛≡ v (P-gen _ a b ¬bRa) a≡b rewrite a≡b = ¬bRa (R-refl v b)

P→¬R : {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → {a b : Candidate} → {v : Preference _R_} → 
        (P v a b) → ¬ (b R a)
P→¬R (P-gen _ _ _ ¬bRa) = ¬bRa

P-trans : {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → {a b c : Candidate} → {v : Preference _R_} → 
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


dec-prefers : {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → (a b : Candidate) → (v : Preference _R_) → Set₁ 
dec-prefers a b v = Dec (P v a b)

prefers? : {Candidate : Set} → {_R_ : Candidate → Candidate → Set} → (a b : Candidate) → (v : Preference _R_) → 
        (dec-prefers a b v)
prefers? a b v with Preference.R-dec v b a | Preference.R-dec v a b | R-complete v a b
... | inj₁ bRa | inj₁ aRb | _ = false because ofⁿ (λ aPb → P→¬R aPb bRa)
... | inj₁ bRa | inj₂ ¬aRb | _ = false because ofⁿ (λ aPb → P→¬R aPb bRa)
... | inj₂ ¬bRa | inj₁ aRb | _ = true because (ofʸ (P-gen v a b ¬bRa))
... | inj₂ ¬bRa | inj₂ ¬aRb | inj₁ aRb = ⊥-elim (¬aRb aRb)
... | inj₂ ¬bRa | inj₂ ¬aRb | inj₂ bRa = ⊥-elim (¬bRa bRa)

Voter→Pref : {Candidate : Set} → (v : Voter) → Preference (r v)
Voter→Pref  = Voter prefs

--- curried version of P for convenience
-}