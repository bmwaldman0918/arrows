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
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Nullary.Decidable.Core using (isYes)
open import VecUtil
open import Data.Nat as ℕ hiding (_≟_)
open import Data.Fin as Fin hiding (splitAt)
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
    record Preference (n : ℕ) (n>1 : n ℕ.> 1) (_R_ : Fin n → Fin n → Set) : Set where
        field
            R-trans    : (a b c : Fin n) → a R b → b R c → a R c
            R-complete : (a b : Fin n)   → (a R b) ⊎   (b R a)
            R-dec      : (a b : Fin n)   → (a R b) ⊎ ¬ (a R b)
    open Preference

    --- Weak preferences are reflexive
    R-refl : (v : Preference n n>1 _R_) 
        → (a : Fin n) 
        ----------------------
        → a R a
    R-refl v a with R-complete v a a
    ... | inj₁ aRa = aRa
    ... | inj₂ aRa = aRa

    ¬R-dec→⊥ : {p : Preference n n>1 _R_} → {a b : Fin n} → ¬ (a R b) → ¬ (b R a) → ⊥
    ¬R-dec→⊥ {p = p} {a = a} {b = b} ¬aRb ¬bRa with R-complete p a b 
    ... | inj₁ aRb = ¬aRb aRb
    ... | inj₂ bRa = ¬bRa bRa
open WeakPreference
open Preference

module StrictPreference where
    --- Strict preferences are the absence of the inverted weak preference
    P : (Preference n n>1 _R_) 
        → (a b : Fin n) 
        ----------------------
        → Set
    P {_R_ = _R_} _ a b = ¬ (b R a)

    --- Strict preferences imply weak preferences
    P→R : {a b : Fin n} 
        → {v : Preference n n>1 _R_} 
        → (P v a b) 
        --------------------------
        → a R b
    P→R {a = a} {b = b} {v = v} ¬bRa with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa = ⊥-elim (¬bRa bRa)

    --- Strict preferences imply inequality
    P↛≡ : {v : Preference n n>1 _R_} 
        → (P v a b) 
        --------------------------
        → ¬ (a ≡ b)
    P↛≡ {b = b} {v = v} ¬bRb a≡b rewrite a≡b = ¬bRb (R-refl v b)

    --- Strict preference is transitive
    P-trans : {v : Preference n n>1 _R_} 
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
    record Voter (n : ℕ) (n>1 : n ℕ.> 1) : Set₁ where
        field
            r : Fin n → Fin n → Set
            prefs : Preference n n>1 r
    open Voter

    --- Strict preference is decidable
    Dec-Prefers : (a b : Fin n) 
                → (v : Preference n n>1 _R_) 
                --------------------------
                → Set
    Dec-Prefers a b v = Dec (P v a b)

    Prefers? : (a b : Fin n) 
            → (v : Voter n n>1)
            ----------------------------
            → (Dec-Prefers {n} {n>1} a b (prefs v))
    Prefers? {n} {n>1} a b v with R-dec {n} {n>1} (prefs v) b a
    ...                 | inj₁ bRa  = false because ofⁿ (λ ¬bRa → ¬bRa bRa)
    ...                 | inj₂ ¬bRa = true  because ofʸ ¬bRa

    --- Strict preference is defined for voters
    Prefers : (a b : Fin n) 
            → (v : Voter n n>1) 
            ---------------
            → Set
    Prefers {n} {n>1} a b record { r = r' ; prefs = prefs' } 
            = P prefs' a b 

    --- Weak preference is decidable
    Dec-weaklyPrefers : (v : Preference n n>1 _R_) 
                    → (a b : Fin n) 
                    ----------------------------
                    → Set
    Dec-weaklyPrefers {_R_ = _R_} v a b = Dec (a R b)

    weaklyPrefers? : (a b : Fin n) 
                    → (v : Voter n n>1)
                    -----------------------------------
                    → (Dec-weaklyPrefers {n} {n>1} (prefs v) a b)
    weaklyPrefers? {n} {n>1} a b v with R-dec {n} {n>1} (prefs v) a b
    ...                  | inj₁ x = true  because ofʸ x
    ...                  | inj₂ y = false because ofⁿ y

    --- Weak preference is defined for voters
    weaklyPrefers : (a b : Fin n) 
                    → (v : Voter n n>1)
                    ---------------
                    → Set
    weaklyPrefers a b record { r = r' ; prefs = prefs' } = r' a b
open VoterBehavior

module Election where
    --- A social preference function contains:
        --- a list of voters
        --- a function that determines an order of candidates
        --- a proof that if all voters agree on a relative ordering of candidates, the function does too
    record SocialPreference (m n : ℕ) (n>1 : n ℕ.> 1) : Set₁ where
        field
            Ballots : Vec (Voter n n>1) m
            SocialPreferenceFunction : Voter n n>1
    open SocialPreference

    --- A voter is decisive if their preference between two candidates implies the election shares that preference
    Decisive : {m n : ℕ}
                → {n>1 : n ℕ.> 1}
                → (a b : Fin n) 
                → (SocialPreference m n n>1) 
                → (v : Voter n n>1) 
                --------------------
                → Set
    Decisive {m} {n} {n>1} a b sp v = Prefers {n} {n>1} a b v → Prefers {n} {n>1} a b (SocialPreferenceFunction sp)

    --- A voter is a dictator if they are decisive over all pairs of candidates
    Dictator : {m n : ℕ} 
                → {n>1 : n ℕ.> 1}
                → (SocialPreference m n n>1) 
                → (v : Voter n n>1) 
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
        → (sp : SocialPreference m n n>1) 
        → (a b : Fin n)
        -------------------------
        → Vec Bool m × Vec Bool m
    VoterPreferences {m} {n} {n>1} e a b 
        = map (λ x → isYes (weaklyPrefers? {n} {n>1} a b x)) (Ballots e) 
        , map (λ x → isYes (weaklyPrefers? {n} {n>1} b a x)) (Ballots e)
open Election

module ProfileIIIVoter where
    data R-one (b : Fin n) (p : Preference n n>1 _R_) : (a c : Fin n) → Set where
        normal  : (a c : Fin n) → ¬ (b ≡ a) → ¬ (b ≡ c) → (a R c) → R-one b p a c
        swapped : (a c : Fin n) →   (b ≡ a) →                       R-one b p a c

    R1-complete : (p : Preference n n>1 _R_) → (b a c : Fin n) → R-one b p a c ⊎ R-one b p c a
    R1-complete p b a c with b ≟ a | b ≟ c | R-complete p a c 
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁ aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₂ cRa = inj₂ (normal c a ¬b≡c ¬b≡a cRa)
    ... | _                      | true because ofʸ   b≡c | _        = inj₂ (swapped c a b≡c)
    ... | true because ofʸ   b≡a | _                      | _        = inj₁ (swapped a c b≡a)

    R1-dec : (p : Preference n n>1 _R_) → (b a c : Fin n) → R-one b p a c ⊎ ¬ (R-one b p a c)
    R1-dec {_R_ = _R_} p b a c with b ≟ a | b ≟ c | R-dec p a c 
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁  aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | true because ofʸ   b≡a | _                      | _         = inj₁ (swapped a c b≡a)
    ... | false because ofⁿ ¬b≡a | _                      | inj₂ ¬aRc = inj₂ λ { (normal .a .c x _ aRc) → ¬aRc aRc
                                                                               ; (swapped .a .c b≡a)    → ¬b≡a b≡a}
    ... | false because ofⁿ ¬b≡a | true because ofʸ   b≡c | inj₁  aRc = inj₂ λ { (normal .a .c _ ¬b≡c _) → ¬b≡c b≡c
                                                                               ; (swapped .a .c b≡a) → ¬b≡a b≡a}

    R1-trans : (p : Preference n n>1 _R_) → (d a b c : Fin n) → R-one d p a b → R-one d p b c → R-one d p a c
    R1-trans p d a b c (normal .a .b ¬d≡a ¬d≡b aRb) (normal .b .c _ ¬d≡c bRc) = normal a c ¬d≡a ¬d≡c (R-trans p a b c aRb bRc)
    R1-trans p d a b c (normal .a .b ¬d≡a ¬d≡b aRb) (swapped .b .c d≡b) = ⊥-elim (¬d≡b d≡b)
    R1-trans p d a b c (swapped .a .b d≡a) _ = swapped a c d≡a

    R1Preference : (p : Preference n n>1 _R_) → (b : Fin n) → Preference n n>1 (R-one b p)
    R1Preference p d = record { R-trans    = R1-trans p d
                              ; R-complete = R1-complete p d 
                              ; R-dec      = R1-dec p d }
    
    Voter→R1Voter : Fin n → Voter n n>1 → Voter n n>1
    Voter→R1Voter {n} {n>1} b record { r = r ; prefs = prefs } = 
        record { r = R-one {n} {n>1} b prefs 
        ; prefs = record { R-trans = R1-trans prefs b 
                         ; R-complete = R1-complete prefs b 
                         ; R-dec = R1-dec prefs b}}

    data R-two (b : Fin n) (p : Preference n n>1 _R_) : (a c : Fin n) → Set where
        normal  : (a c : Fin n) → ¬ (b ≡ a) → ¬ (b ≡ c) → (a R c) → R-two b p a c
        swapped : (a c : Fin n) →   (b ≡ a) →                       R-two b p c a

    R2-complete : (p : Preference n n>1 _R_) → (b a c : Fin n) → R-two b p a c ⊎ R-two b p c a
    R2-complete p b a c with b ≟ a | b ≟ c | R-complete p a c 
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁ aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₂ cRa = inj₂ (normal c a ¬b≡c ¬b≡a cRa)
    ... | _                      | true because ofʸ   b≡c | _        = inj₁ (swapped c a b≡c)
    ... | true because ofʸ   b≡a | _                      | _        = inj₂ (swapped a c b≡a)

    R2-dec : (p : Preference n n>1 _R_) → (b a c : Fin n) → R-two b p a c ⊎ ¬ (R-two b p a c)
    R2-dec {_R_ = _R_} p b a c with b ≟ a | b ≟ c | R-dec p a c     
    ... | false because ofⁿ ¬b≡a | false because ofⁿ ¬b≡c | inj₁  aRc = inj₁ (normal a c ¬b≡a ¬b≡c aRc)
    ... | _                      | true because ofʸ   b≡c | _         = inj₁ (swapped c a b≡c)
    ... | _                      | false because ofⁿ ¬b≡c | inj₂ ¬aRc = inj₂ λ { (normal .a .c _ _ aRc) → ¬aRc aRc
                                                                               ; (swapped .c .a b≡c) → ¬b≡c b≡c }
    ... | true because ofʸ   b≡a | false because ofⁿ ¬b≡c | _         = inj₂ λ { (normal .a .c ¬b≡a _ _) → ¬b≡a b≡a
                                                                               ; (swapped .c .a b≡c) → ¬b≡c b≡c }

    R2-trans : (p : Preference n n>1 _R_) → (d a b c : Fin n) → R-two d p a b → R-two d p b c → R-two d p a c
    R2-trans p d a b c (normal .a .b ¬d≡a ¬d≡b aRb) (normal .b .c _ ¬d≡c bRc) = normal a c ¬d≡a ¬d≡c (R-trans p a b c aRb bRc)
    R2-trans p d a b c (swapped .b .a d≡b) (normal .b .c ¬d≡b ¬d≡c bRc) = ⊥-elim (¬d≡b d≡b)
    R2-trans p d a b c _ (swapped .c .b d≡c) = swapped c a d≡c

    R2Preference : (p : Preference n n>1 _R_) → (b : Fin n) → Preference n n>1 (R-two b p)
    R2Preference {n = n} p d = record { R-trans    = R2-trans p d
                                      ; R-complete = R2-complete p d 
                                      ; R-dec      = R2-dec p d }

    Voter→R2Voter : {n>1 : n ℕ.> 1} → Fin n → Voter n n>1 → Voter n n>1
    Voter→R2Voter {n} {n>1} b record { r = r ; prefs = prefs } = 
        record { r = R-two {n} {n>1} b prefs 
        ; prefs = record { R-trans = R2-trans prefs b 
                         ; R-complete = R2-complete prefs b 
                         ; R-dec = R2-dec prefs b}}

    data Pivot (a b : Fin n) (p : Preference n n>1 _R_) : (c d : Fin n) → Set where
        normal   : (c d : Fin n) → ¬ (a ≡ c) → ¬ (a ≡ d) → ¬ (b ≡ c) → ¬ (b ≡ d) → (c R d) → Pivot a b p c d
        a-first  : (c d : Fin n) →   (a ≡ c) →                                               Pivot a b p c d
        b-second : (c d : Fin n) →   (b ≡ c) → ¬ (a ≡ d) →                                   Pivot a b p c d
    
    Pivot-complete : (p : Preference n n>1 _R_) → (a b c d : Fin n) → Pivot a b p c d ⊎ Pivot a b p d c
    Pivot-complete p a b c d with a ≟ c | a ≟ d | b ≟ c | b ≟ d | R-complete p c d 
    ... | true because ofʸ a≡c | _ | _ | _ | _ = inj₁ (a-first c d a≡c) 
    ... | _ | true because ofʸ a≡d | _ | _ | _ = inj₂ (a-first d c a≡d)
    ... | _ | false because ofⁿ ¬a≡d | true because ofʸ b≡c | _ | _ = inj₁ (b-second c d b≡c ¬a≡d)
    ... | false because ofⁿ ¬a≡c | _ | _ | true because ofʸ b≡d | _ = inj₂ (b-second d c b≡d ¬a≡c)
    ... | false because ofⁿ ¬a≡c | false because ofⁿ ¬a≡d | false because ofⁿ ¬b≡c | false because ofⁿ ¬b≡d | inj₁ cRd = inj₁ (normal c d ¬a≡c ¬a≡d ¬b≡c ¬b≡d cRd)
    ... | false because ofⁿ ¬a≡c | false because ofⁿ ¬a≡d | false because ofⁿ ¬b≡c | false because ofⁿ ¬b≡d | inj₂ dRc = inj₂ (normal d c ¬a≡d ¬a≡c ¬b≡d ¬b≡c dRc) 

    Pivot-decidable : (p : Preference n n>1 _R_) → (a b c d : Fin n) → Pivot a b p c d ⊎ ¬ (Pivot a b p c d)
    Pivot-decidable p a b c d with a ≟ c | a ≟ d | b ≟ c | b ≟ d | R-dec p c d
    ... | true because ofʸ a≡c | _ | _ | _ | _ = inj₁ (a-first c d a≡c)
    ... | _ | false because ofⁿ ¬a≡d | true because ofʸ b≡c | _ | _ = inj₁ (b-second c d b≡c ¬a≡d)
    ... | false because ofⁿ ¬a≡c | false because ofⁿ ¬a≡d | false because ofⁿ ¬b≡c | false because ofⁿ ¬b≡d | inj₁ cRd = inj₁ (normal c d ¬a≡c ¬a≡d ¬b≡c ¬b≡d cRd)
    ... | false because ofⁿ ¬a≡c | _ | false because ofⁿ ¬b≡c | true because ofʸ b≡d | _ = inj₂ λ { (normal .c .d _ _ _ ¬b≡d _) → ¬b≡d b≡d
                                                                                                  ; (a-first .c .d a≡c) → ¬a≡c a≡c
                                                                                                  ; (b-second .c .d b≡c _) → ¬b≡c b≡c }
    ... | false because ofⁿ ¬a≡c | true because ofʸ a≡d | _ | true because ofʸ b≡d | _ = inj₂ λ { (normal .c .d _ _ _ ¬b≡d _) → ¬b≡d b≡d
                                                                                                ; (a-first .c .d a≡c) → ¬a≡c a≡c
                                                                                                ; (b-second .c .d _ ¬a≡d) → ¬a≡d a≡d }
    ... | false because ofⁿ ¬a≡c | true because ofʸ a≡d | _ | _ | _ = inj₂ λ { (normal .c .d _ ¬a≡d _ _ _) → ¬a≡d a≡d
                                                                             ; (a-first .c .d a≡c) → ¬a≡c a≡c
                                                                             ; (b-second .c .d _ ¬a≡d) → ¬a≡d a≡d }
    ... | false because ofⁿ ¬a≡c | _ | false because ofⁿ ¬b≡c | _ | inj₂ ¬cRd = inj₂ λ {(normal .c .d _ _ _ _ cRd) → ¬cRd cRd
                                                                                       ; (a-first .c .d a≡c) → ¬a≡c a≡c
                                                                                       ; (b-second .c .d b≡c _) → ¬b≡c b≡c}
    Pivot-trans : (p : Preference n n>1 _R_) → (a b c d e : Fin n) → Pivot a b p c d → Pivot a b p d e → Pivot a b p c e
    Pivot-trans p a b c d e (normal .c .d ¬a≡c ¬a≡d ¬b≡c ¬b≡d cRd) (normal .d .e _ ¬a≡e _ ¬b≡e dRe) = normal c e ¬a≡c ¬a≡e ¬b≡c ¬b≡e (R-trans p c d e cRd dRe)
    Pivot-trans p a b c d e (normal .c .d _ ¬a≡d _ _ _) (a-first .d .e a≡d) = ⊥-elim (¬a≡d a≡d)
    Pivot-trans p a b c d e (normal .c .d _ _ _ ¬b≡d _) (b-second .d .e b≡d _) = ⊥-elim (¬b≡d b≡d)
    Pivot-trans p a b c d e (a-first .c .d a≡c) _ = a-first c e a≡c
    Pivot-trans p a b c d e (b-second .c .d b≡c _) (normal .d .e _ ¬a≡e _ _ _) = b-second c e b≡c ¬a≡e
    Pivot-trans p a b c d e (b-second .c .d _ ¬a≡d) (a-first .d .e a≡d) = ⊥-elim (¬a≡d a≡d)
    Pivot-trans p a b c d e (b-second .c .d b≡c _) (b-second .d .e _ ¬a≡e) = b-second c e b≡c ¬a≡e
    
    Voter→PivotalVoter : {n>1 : n ℕ.> 1} → Fin n → Fin n → Voter n n>1 → Voter n n>1
    Voter→PivotalVoter {n} {n>1} a b record { r = r ; prefs = prefs } = 
                        record { r = Pivot {n} {n>1} a b prefs 
                                ; prefs = record { R-trans = Pivot-trans prefs a b
                                                 ; R-complete = Pivot-complete prefs a b
                                                 ; R-dec = Pivot-decidable prefs a b}}