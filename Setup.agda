module Setup where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec
open import Data.Vec.Relation.Unary.All as All using (All)
open import Relation.Unary using (Pred; ∁; _⊆_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false; Bool)
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable.Core using (isYes)
open import VecUtil
open import Data.Nat as ℕ hiding (_≟_)
open import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)

private
    variable
        n : ℕ
        n>1 : n ℕ.> 1
        a b c : Fin n
        _R_ : Fin n → Fin n → Set

module WeakPreference where
    --- A weak preference is transitive, complete, and decidable relation
    --- A weak preference is not anti-symmetric, so voters can be indifferent between candidates
    record Preference {n : ℕ} {n>1 : n ℕ.> 1} (_R_ : Fin n → Fin n → Set) : Set where
        field
            R-trans    : (a b c : Fin n) → a R b → b R c → a R c
            R-complete : (a b : Fin n)   → (a R b) ⊎   (b R a)
            R-dec      : (a b : Fin n)   → (a R b) ⊎ ¬ (a R b)
    open Preference

    --- Weak preferences are reflexive
    R-refl : (v : Preference {n>1 = n>1} _R_) 
        → (a : Fin n) 
        ----------------------
        → a R a
    R-refl v a with R-complete v a a
    ... | inj₁ aRa = aRa
    ... | inj₂ aRa = aRa

    ¬R-dec→⊥ : {p : Preference {n} {n>1} _R_} → {a b : Fin n} → ¬ (a R b) → ¬ (b R a) → ⊥
    ¬R-dec→⊥ {p = p} {a = a} {b = b} ¬aRb ¬bRa with R-complete p a b 
    ... | inj₁ aRb = ¬aRb aRb
    ... | inj₂ bRa = ¬bRa bRa
open WeakPreference
open Preference

module StrictPreference where
    --- Strict preferences are the absence of the inverted weak preference
    P : (Preference {n} {n>1} _R_) 
        → (a b : Fin n) 
        ----------------------
        → Set
    P {_R_ = _R_} _ a b = ¬ (b R a)

    --- Strict preferences imply weak preferences
    P→R : {a b : Fin n} 
        → {v : Preference {n} {n>1} _R_} 
        → (P v a b) 
        --------------------------
        → a R b
    P→R {a = a} {b = b} {v = v} ¬bRa with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa = ⊥-elim (¬bRa bRa)

    --- Strict preferences imply inequality
    P↛≡ : {v : Preference {n} {n>1} _R_} 
        → (P v a b) 
        --------------------------
        → ¬ (a ≡ b)
    P↛≡ {b = b} {v = v} ¬bRb a≡b rewrite a≡b = ¬bRb (R-refl v b)

    --- Strict preference is transitive
    P-trans : {v : Preference {n} {n>1} _R_} 
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
            prefs : Preference {n} {n>1} r
    open Voter

    --- Strict preference is decidable
    Dec-Prefers : (a b : Fin n) 
                → (v : Preference {n} {n>1} _R_) 
                --------------------------
                → Set
    Dec-Prefers a b v = Dec (P v a b)

    Prefers? : (a b : Fin n) 
            → (v : Voter)
            ----------------------------
            → (Dec-Prefers {n} {n>1} a b (prefs v))
    Prefers? {n} {n>1} a b v with R-dec {n} {n>1} (prefs v) b a
    ...                 | inj₁ bRa  = false because ofⁿ (λ ¬bRa → ¬bRa bRa)
    ...                 | inj₂ ¬bRa = true  because ofʸ ¬bRa

    --- Strict preference is defined for voters
    Prefers : {n>1 : n ℕ.> 1} 
            → (a b : Fin n) 
            → (v : Voter) 
            ---------------
            → Set
    Prefers {n} {n>1} a b record { r = r' ; prefs = prefs' } 
            = P (prefs' {n} {n>1}) a b

    --- Weak preference is decidable
    Dec-weaklyPrefers : (v : Preference {n} {n>1} _R_) 
                    → (a b : Fin n) 
                    ----------------------------
                    → Set
    Dec-weaklyPrefers {_R_ = _R_} v a b = Dec (a R b)

    weaklyPrefers? : (a b : Fin n) 
                    → (v : Voter)
                    -----------------------------------
                    → (Dec-weaklyPrefers {n} {n>1} (prefs v) a b)
    weaklyPrefers? {n} {n>1} a b v with R-dec {n} {n>1} (prefs v) a b
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
    record SocialPreference {m : ℕ} : Set₁ where
        field
            Ballots : Vec (Voter) (suc m)
            SocialPreferenceFunction : Voter
            Unanimity : (a b : Fin n) → All (Prefers {n} {n>1} a b) Ballots → (Prefers {n} {n>1} a b SocialPreferenceFunction)
            --- TODO DEFINE ONE Unanimity IN TERMS OF OTHER
            weakUnanimity : (a b : Fin n) → All (weaklyPrefers a b) Ballots → (weaklyPrefers a b SocialPreferenceFunction)
    open SocialPreference

    --- A voter is decisive if their preference between two candidates implies the election shares that preference
    Decisive : {m n : ℕ}
                → {n>1 : n ℕ.> 1}
                → (a b : Fin n) 
                → (SocialPreference {m}) 
                → (v : Voter) 
                --------------------
                → Set
    Decisive {m} {n} {n>1} a b sp v = Prefers {n} {n>1} a b v → Prefers {n} {n>1} a b (SocialPreferenceFunction sp)

    --- A voter is a dictator if they are decisive over all pairs of candidates
    Dictator : {m n : ℕ} 
                → {n>1 : n ℕ.> 1}
                → (SocialPreference {m}) 
                → (v : Voter) 
                --------------------
                → Set
    Dictator {m} {n} {n>1} sp v = ∀ (a b : Fin n) → Decisive {m} {n} {n>1} a b sp v

    --- utility predicates for list operations
    C-P⊆wP :  {n : ℕ} 
            → {n>1 : n ℕ.> 1}
            → (a b : Fin n)
            ----------------------------------------
            → (∁ (Prefers {n} {n>1} a b)) ⊆ weaklyPrefers b a
    C-P⊆wP {n} {n>1} a b {record { r = r' ; prefs = prefs' }} x 
            with (R-dec {n} {n>1} prefs') b a
    ...     | inj₁ y = y 
    ...     | inj₂ z = ⊥-elim (x z)

    wP⊆C-P :  {n : ℕ} 
            → {n>1 : n ℕ.> 1}
            → (a b : Fin n)
            ----------------------------------------
            → weaklyPrefers b a ⊆ (∁ (Prefers {n} {n>1} a b))
    wP⊆C-P {n} {n>1} a b {v} x 
            with Prefers? {n} {n>1} a b v 
    ... | false because ofⁿ ¬p = λ y → y x 
    ... | true  because ofʸ  p = λ _ → p x 

    --- function that defines the preferences of all voters across two candidates
    VoterPreferences : {m n : ℕ} 
        → {n>1 : n ℕ.> 1}
        → (sp : SocialPreference {m}) 
        → (a b : Fin n)
        -------------------------
        → Vec Bool (suc m) × Vec Bool (suc m)
    VoterPreferences {m} {n} {n>1} e a b 
        = map (λ x → isYes (weaklyPrefers? {n} {n>1} a b x)) (Ballots e) 
        , map (λ x → isYes (weaklyPrefers? {n} {n>1} b a x)) (Ballots e)
open Election

module ProfileIIIVoter where
    data R-one (b : Fin n) (p : Preference {n} {n>1} _R_) : (a c : Fin n) → Set where
        normal  : (a c : Fin n) → ¬ (b ≡ a) → ¬ (b ≡ c) → (a R c) → R-one b p a c
        swapped : (a c : Fin n) →   (b ≡ a) →                       R-one b p a c

    R1-complete : (p : Preference {n} {n>1} _R_) → (b a c : Fin n) → R-one b p a c ⊎ R-one b p c a
    R1-complete p b a c with b ≟ a | b ≟ c | R-complete p a c 
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁ aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₂ cRa = inj₂ (normal c a ¬b≡c ¬b≡a cRa)
    ... | _                      | true because ofʸ   b≡c | _        = inj₂ (swapped c a b≡c)
    ... | true because ofʸ   b≡a | _                      | _        = inj₁ (swapped a c b≡a)

    R1-dec : (p : Preference {n} {n>1} _R_) → (b a c : Fin n) → R-one b p a c ⊎ ¬ (R-one b p a c)
    R1-dec {_R_ = _R_} p b a c with b ≟ a | b ≟ c | R-dec p a c 
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁  aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | true because ofʸ   b≡a | _                      | _         = inj₁ (swapped a c b≡a)
    ... | false because ofⁿ ¬b≡a | _                      | inj₂ ¬aRc = inj₂ λ { (normal .a .c x _ aRc) → ¬aRc aRc
                                                                               ; (swapped .a .c b≡a)    → ¬b≡a b≡a}
    ... | false because ofⁿ ¬b≡a | true because ofʸ   b≡c | inj₁  aRc = inj₂ λ { (normal .a .c _ ¬b≡c _) → ¬b≡c b≡c
                                                                               ; (swapped .a .c b≡a) → ¬b≡a b≡a}

    R1-trans : (p : Preference {n} {n>1} _R_) → (d a b c : Fin n) → R-one d p a b → R-one d p b c → R-one d p a c
    R1-trans p d a b c (normal .a .b ¬d≡a ¬d≡b aRb) (normal .b .c _ ¬d≡c bRc) = normal a c ¬d≡a ¬d≡c (R-trans p a b c aRb bRc)
    R1-trans p d a b c (normal .a .b ¬d≡a ¬d≡b aRb) (swapped .b .c d≡b) = ⊥-elim (¬d≡b d≡b)
    R1-trans p d a b c (swapped .a .b d≡a) _ = swapped a c d≡a

    R1Preference : (p : Preference {n} {n>1} _R_) → (b : Fin n) → Preference {n} {n>1} (R-one b p)
    R1Preference {n = n} p d = record { R-trans    = R1-trans p d
                                      ; R-complete = R1-complete p d 
                                      ; R-dec      = R1-dec p d }

    data R-two (b : Fin n) (p : Preference {n} {n>1} _R_) : (a c : Fin n) → Set where
        normal  : (a c : Fin n) → ¬ (b ≡ a) → ¬ (b ≡ c) → (a R c) → R-two b p a c
        swapped : (a c : Fin n) →   (b ≡ a) →                       R-two b p c a

    R2-complete : (p : Preference {n} {n>1} _R_) → (b a c : Fin n) → R-two b p a c ⊎ R-two b p c a
    R2-complete p b a c with b ≟ a | b ≟ c | R-complete p a c 
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁ aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₂ cRa = inj₂ (normal c a ¬b≡c ¬b≡a cRa)
    ... | _                      | true because ofʸ   b≡c | _        = inj₁ (swapped c a b≡c)
    ... | true because ofʸ   b≡a | _                      | _        = inj₂ (swapped a c b≡a)

    R2-dec : (p : Preference {n} {n>1} _R_) → (b a c : Fin n) → R-two b p a c ⊎ ¬ (R-two b p a c)
    R2-dec {_R_ = _R_} p b a c with b ≟ a | b ≟ c | R-dec p a c     
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁  aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | _                      | true because ofʸ   b≡c | _         = inj₁ (swapped c a b≡c)
    ... | _                      | false because ofⁿ ¬b≡c | inj₂ ¬aRc = inj₂ λ { (normal .a .c _ _ aRc) → ¬aRc aRc
                                                                               ; (swapped .c .a b≡c) → ¬b≡c b≡c }
    ... | true because ofʸ   b≡a | false because ofⁿ ¬b≡c | _         = inj₂ λ { (normal .a .c ¬b≡a _ _) → ¬b≡a b≡a
                                                                               ; (swapped .c .a b≡c) → ¬b≡c b≡c }

    R2-trans : (p : Preference {n} {n>1} _R_) → (d a b c : Fin n) → R-two d p a b → R-two d p b c → R-two d p a c
    R2-trans p d a b c (normal .a .b ¬d≡a ¬d≡b aRb) (normal .b .c _ ¬d≡c bRc) = normal a c ¬d≡a ¬d≡c (R-trans p a b c aRb bRc)
    R2-trans p d a b c (swapped .b .a d≡b) (normal .b .c ¬d≡b ¬d≡c bRc) = ⊥-elim (¬d≡b d≡b)
    R2-trans p d a b c _ (swapped .c .b d≡c) = swapped c a d≡c

    R2Preference : (p : Preference {n} {n>1} _R_) → (b : Fin n) → Preference {n} {n>1} (R-two b p)
    R2Preference {n = n} p d = record { R-trans    = R2-trans p d
                                      ; R-complete = R2-complete p d 
                                      ; R-dec      = R2-dec p d }