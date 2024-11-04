module Setup where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Relation.Unary using (Pred; ∁; _⊆_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false; Bool)
open import Data.List.Relation.Unary.Any as Any using (Any; any?)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable.Core using (isYes)
open import ListUtil
open import Data.Nat as ℕ
open import Data.Fin

private
    variable
        n : ℕ
        a b c : Fin n
        _R_ : Fin n → Fin n → Set

module WeakPreference where
    --- A weak preference is transitive, complete, and decidable relation
    --- A weak preference is not anti-symmetric, so voters can be indifferent between candidates
    record Preference {n : ℕ} (_R_ : Fin n → Fin n → Set) : Set where
        field
            R-trans    : (a b c : Fin n) → a R b → b R c → a R c
            R-complete : (a b : Fin n)   → (a R b) ⊎   (b R a)
            R-dec      : (a b : Fin n)   → (a R b) ⊎ ¬ (a R b)
    open Preference

    --- Weak preferences are reflexive
    R-refl : (v : Preference _R_) 
        → (a : Fin n) 
        ----------------------
        → a R a
    R-refl v a with R-complete v a a
    ... | inj₁ aRa = aRa
    ... | inj₂ aRa = aRa
open WeakPreference
open Preference

module StrictPreference where
    --- Strict preferences are the absence of the inverted weak preference
    P : (Preference {n} _R_) 
        → (a b : Fin n) 
        ----------------------
        → Set
    P {_R_ = _R_} _ a b = ¬ (b R a)

    --- Strict preferences imply weak preferences
    P→R : {a b : Fin n} 
        → {v : Preference {n} _R_} 
        → (P v a b) 
        --------------------------
        → a R b
    P→R {a = a} {b = b} {v = v} ¬bRa with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa = ⊥-elim (¬bRa bRa)

    --- Strict preferences imply inequality
    P↛≡ : {v : Preference {n} _R_} 
        → (P v a b) 
        --------------------------
        → ¬ (a ≡ b)
    P↛≡ {b = b} {v = v} ¬bRb a≡b rewrite a≡b = ¬bRb (R-refl v b)

    --- Strict preference is transitive
    P-trans : {v : Preference {n} _R_} 
            → P v a b 
            → P v b c 
            --------------------------
            → P v a c
    P-trans {a = a} {b = b} {c = c} {v = v} 
        with (R-dec v a b) | (R-complete v a b) 
    ...      | inj₁ aRb    | _                 = λ  bRc ¬cRb cRa → ¬cRb (R-trans v c a b cRa aRb)
    ...      | inj₂ ¬aRb   | inj₁ aRb          = λ ¬bRa ¬cRb cRa → ⊥-elim (¬aRb aRb)
    ...      | _           | inj₂ bRa          = λ ¬bRa ¬cRb cRa → ⊥-elim (¬bRa bRa)
open StrictPreference

module VoterBehavior where
    --- A voter is a weak preference organized in a specific way for convenience
    record Voter : Set₁ where
        field
            r : Fin n → Fin n → Set
            prefs : Preference {n} r
    open Voter

    --- Strict preference is decidable
    Dec-Prefers : (a b : Fin n) 
                → (v : Preference {n} _R_) 
                --------------------------
                → Set
    Dec-Prefers a b v = Dec (P v a b)

    Prefers? : (a b : Fin n) 
            → (v : Voter)
            ----------------------------
            → (Dec-Prefers a b (prefs v))
    Prefers? a b v with R-dec (prefs v) b a
    ...                 | inj₁ bRa  = false because ofⁿ (λ ¬bRa → ¬bRa bRa)
    ...                 | inj₂ ¬bRa = true  because ofʸ ¬bRa

    --- Strict preference is defined for voters
    Prefers : (a b : Fin n) 
            → (v : Voter) 
            ---------------
            → Set
    Prefers a b record { r = r' ; prefs = prefs' }
                    = P {_R_ = r'} prefs' a b

    --- Weak preference is decidable
    Dec-weaklyPrefers : (v : Preference {n} _R_) 
                    → (a b : Fin n) 
                    ----------------------------
                    → Set
    Dec-weaklyPrefers {_R_ = _R_} v a b = Dec (a R b)

    weaklyPrefers? : (a b : Fin n) 
                    → (v : Voter)
                    -----------------------------------
                    → (Dec-weaklyPrefers (prefs v) a b)
    weaklyPrefers? a b v with R-dec (prefs v) a b
    ...                  | inj₁ x = true  because ofʸ x
    ...                  | inj₂ y = false because ofⁿ y

    --- Weak preference is defined for voters
    weaklyPrefers : (a b : Fin n) 
                    → (v : Voter)
                    ---------------
                    → Set
    weaklyPrefers a b record { r = r' ; prefs = prefs' } = r' a b
open VoterBehavior

module Election where
    --- A social preference function contains:
        --- a list of voters
        --- a function that determines an order of candidates
        --- a proof that if all voters agree on a relative ordering of candidates, the function does too
    record SocialPreference : Set₁ where
        field
            Ballots : List⁺ (Voter)
            SocialPreferenceFunction : Voter
            Unanimity : (a b : Fin n) → All (Prefers a b) (toList Ballots) → (Prefers a b SocialPreferenceFunction)
            --- TODO DEFINE ONE Unanimity IN TERMS OF OTHER
            weakUnanimity : (a b : Fin n) → All (weaklyPrefers a b) (toList Ballots) → (weaklyPrefers a b SocialPreferenceFunction)
    open SocialPreference

    --- A voter is decisive if their preference between two candidates implies the election shares that preference
    Decisive : (a b : Fin n) 
                → (SocialPreference) 
                → (v : Voter) 
                --------------------
                → Set
    Decisive a b sp v = Prefers a b v → Prefers a b (SocialPreferenceFunction sp)

    --- A voter is a dictator if they are decisive over all pairs of candidates
    Dictator : {n : ℕ} 
                → (SocialPreference) 
                → (v : Voter) 
                --------------------
                → Set
    Dictator {n = n} sp v = ∀ (a b : Fin n) → Decisive a b sp v

    --- utility predicates for list operations
    C-P⊆wP :  {n : ℕ} 
            → (a b : Fin n)
            ----------------------------------------
            → (∁ (Prefers a b)) ⊆ weaklyPrefers b a
    C-P⊆wP {n = n} a b {record { r = r' ; prefs = prefs' }} x 
            with (R-dec prefs') b a
    ...     | inj₁ y = y 
    ...     | inj₂ z = ⊥-elim (x z)

    wP⊆C-P :  {n : ℕ} 
            → (a b : Fin n)
            ----------------------------------------
            → weaklyPrefers b a ⊆ (∁ (Prefers a b))
    wP⊆C-P a b {v} x 
            with Prefers? a b v 
    ... | false because ofⁿ ¬p = λ y → y x 
    ... | true  because ofʸ  p = λ _ → p x 

    --- function that defines the preferences of all voters across two candidates
    VoterPreferences : {n : ℕ} 
        → (sp : SocialPreference) 
        → (a b : Fin n)
        -------------------------
        → List⁺ Bool × List⁺ Bool
    VoterPreferences e a b 
        = map (λ x → isYes (weaklyPrefers? a b x)) (Ballots e) 
        , map (λ x → isYes (weaklyPrefers? b a x)) (Ballots e)
open Election