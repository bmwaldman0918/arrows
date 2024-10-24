module Setup where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false)

private
    variable
        Candidate : Set
        a b c : Candidate
        _R_ : Candidate → Candidate → Set

--- definitions and properties of weak preference

record Preference {Candidate : Set} (_R_ : Candidate → Candidate → Set) : Set where
    field
        R-trans : a R b → b R c → a R c
        R-complete : (a R b) ⊎ (b R a)
        R-dec : (a R b) ⊎ ¬ (a R b)
open Preference

R-refl : (v : Preference _R_) → (a : Candidate) → a R a
R-refl v a with R-complete v {a} 
... | inj₁ aRa = aRa
... | inj₂ aRa = aRa

--- definitions and properties of strict preference 
P : (Preference {Candidate} _R_) → (a b : Candidate) → Set
P {_R_ = _R_} _ a b = ¬ (b R a)

P→R : {a b : Candidate} → {v : Preference _R_} → (P v a b) → a R b
P→R {a = a} {b = b} {v = v} ¬bRa with R-complete v {a} {b} 
... | inj₁ aRb = aRb
... | inj₂ bRa = ⊥-elim (¬bRa bRa)

P↛≡ : {v : Preference _R_} → (P v a b) → ¬ (a ≡ b)
P↛≡ {b = b} {v = v} ¬bRb a≡b rewrite a≡b = ¬bRb (R-refl v b)

P-trans : {v : Preference _R_} → P v a b → P v b c → P v a c
P-trans {a = a} {b = b} {c = c} {v = v} with (R-dec v {a} {b})
                                            | (R-complete v {a} {b}) 
... | inj₁ aRb  | _        = λ bRc ¬cRb cRa → ¬cRb (R-trans v cRa aRb)
... | inj₂ ¬aRb | inj₁ aRb = λ ¬bRa ¬cRb cRa → ⊥-elim (¬aRb aRb)
... | _         | inj₂ bRa = λ ¬bRa ¬cRb cRa → ⊥-elim (¬bRa bRa)

--- functions related to voter preference
record Voter {Candidate : Set} : Set₁ where
    field
        r : Candidate → Candidate → Set
        prefs : Preference r
open Voter

Dec-Prefers : (v : Preference {Candidate} _R_) → (a b : Candidate) → Set
Dec-Prefers v a b = Dec (P v a b)

Prefers? : (a b : Candidate) → (v : Voter {Candidate}) → (Dec-Prefers (prefs v) a b)
Prefers? a b v with R-dec (prefs v) {b} {a}
... | inj₁ bRa  = false because (ofⁿ (λ ¬bRa → ¬bRa bRa))
... | inj₂ ¬bRa = true because ofʸ ¬bRa

--- curried version of P for convenience
Prefers : (a b : Candidate) → (v : Voter {Candidate}) → Set
Prefers a b record { r = r' ; prefs = prefs' } = P {_R_ = r'} prefs' a b

Dec-weaklyPrefers : (v : Preference {Candidate} _R_) → (a b : Candidate) → Set
Dec-weaklyPrefers {_R_ = _R_} v a b = Dec (a R b)

weaklyPrefers : (a b : Candidate) → (v : Voter {Candidate}) → Set
weaklyPrefers a b record { r = r' ; prefs = prefs' } = r' a b

weaklyPrefers? : (a b : Candidate) → (v : Voter {Candidate}) → (Dec-weaklyPrefers (prefs v) a b)
weaklyPrefers? a b v with R-dec (prefs v) {a} {b}
... | inj₁ x = true because ofʸ x
... | inj₂ y = false because ofⁿ y

record SocialPreference {Candidate : Set} : Set₁ where
    field
        Ballots : List⁺ (Voter {Candidate})
        SocialPreferenceFunction : Voter {Candidate}
        Unanimity : (a b : Candidate) → All (weaklyPrefers a b) (toList Ballots) → (weaklyPrefers a b SocialPreferenceFunction)
open SocialPreference

Decisive : (a b : Candidate) → (SocialPreference) → (v : Voter) → Set
Decisive a b sp v = Prefers a b v → Prefers a b (SocialPreferenceFunction sp)

Dictator : (SocialPreference {Candidate}) → (v : Voter {Candidate}) → Set
Dictator {Candidate} sp v = ∀ (a b : Candidate) → Decisive a b sp v