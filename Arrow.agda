open import Setup
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList; _∷_)
open import Data.List using (_∷_; List)
open import Data.List.Relation.Unary.All using (All; []; all?; uncons; map)
open import Data.List.Relation.Unary.Any as Any using (Any; any?; here; there; satisfied; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Bool using (true; false)
open import Data.Empty
open import ListUtil
open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Nat as ℕ
open import Data.Fin

module Arrow where
open SocialPreference

private
    variable
        n : ℕ
        a b c : Fin n
        
postulate 
    IndependenceOfIrrelevantAlternatives : {n : ℕ} 
        → {e1 e2 : SocialPreference} 
        → VoterPreferences {n} e1 ≡ VoterPreferences e2
        → Prefers a b (SocialPreferenceFunction e1) 
          -----------------------------------------
        → Prefers a b (SocialPreferenceFunction e2)

ExistsPivot : (election : SocialPreference) → Any (Decisive a b election) (toList (SocialPreference.Ballots election))
ExistsPivot {a = a} {b = b} election with all? (Prefers? a b) (toList (SocialPreference.Ballots election)) | (Prefers? a b) (SocialPreference.SocialPreferenceFunction election)
... |  _                            | true because ofʸ election-aPb = here (λ x election-bRa → election-aPb election-bRa)
... | true because ofʸ p            | false because ofⁿ ¬election-aPb = ⊥-elim (¬election-aPb (SocialPreference.Unanimity election a b p))
... | false because ofⁿ ¬all-aPb    | false because ofⁿ ¬election-bRa with ¬AllP→AnyCP (Prefers? a b) ¬all-aPb 
... | any-bRa = Any.map (λ x v-aPb election-bRa → x v-aPb) any-bRa

--- cases!
--- first, non b cases
--- assume pivot a > c
--- pivot a > b implies a > b
--- create new profile such that for all voters b > a implies b > c and a > b implies c > b
--- moving b cannot change opinion of a vs c 
--- we need IIA postulate
--- IIA -- from an election we can construct a list of voters preferences for two candidates
--- IIA says if the elections have the same list of voter prefs, same spf pref

--- how to manipulate elections to change preferences of voters in them/profile switching stuff

swap-ab : (a b : Fin n) → Voter → Voter
swap-ab {n = n} a b record { r = r ; prefs = prefs } with prefs {n}
... | record { R-trans = R-trans ; R-complete = R-complete ; R-dec = R-dec } 
    = record { prefs = record { R-dec = λ a' b' → {!   !} ; R-complete = {!   !} }}

aDb→aDc : {v : Voter} → (election : SocialPreference) → (Decisive a b election v) → (Decisive a c election v)
aDb→aDc {a = a} {b = b} {c = c} e aDb v-aPc with Prefers? a c (SocialPreference.SocialPreferenceFunction e) 
... | false because ofⁿ ¬p = {!   !}
... | true because ofʸ p = p

arrows-theorem : (election : SocialPreference) → Any (Dictator {n} election) (toList (SocialPreference.Ballots election))
arrows-theorem e = {!   !}