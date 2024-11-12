module Arrow where

open import Setup
open Election
open VoterBehavior
open SocialPreference

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Relation.Unary.All using (All; []; all?; uncons; map)
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?; here; there; satisfied; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Bool using (true; false)
open import Data.Empty
open import VecUtil
open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Nat as ℕ using (ℕ; _>_)
open import Data.Fin

private
    variable
        m n : ℕ
        m>0 : m ℕ.> 0
        a b c : Fin n
        
postulate 
    IndependenceOfIrrelevantAlternatives :  {e1 e2 : SocialPreference} 
        → VoterPreferences {m} {n} e1 ≡ VoterPreferences e2
        → Prefers a b (SocialPreferenceFunction e1) 
          -----------------------------------------
        → Prefers a b (SocialPreferenceFunction e2)

ExistsPivot : (election : SocialPreference {n}) → Any (Decisive a b election) (SocialPreference.Ballots election)
ExistsPivot {a = a} {b = b} election with all? (Prefers? a b) (SocialPreference.Ballots election) | (Prefers? a b) (SocialPreference.SocialPreferenceFunction election) 
ExistsPivot {n} {a = a} {b = b} election  | false because ofⁿ ¬p | true because ofʸ p = {!   !}
... | true because ofʸ p | .true because ofʸ p₁ = {!   !}
... | true because ofʸ p | .false because ofⁿ ¬p = {!   !}
ExistsPivot {ℕ.zero} {a = a} {b = b} election | false because ofⁿ ¬all-aPb | false because ofⁿ ¬p₁ with SocialPreference.Ballots election
... | y = {!   !}
ExistsPivot {ℕ.suc n} {a = a} {b = b} election | false because ofⁿ ¬all-aPb | false because ofⁿ ¬p₁ with ¬AllP→AnyCP {m>0 = ℕ.s≤s ℕ.z≤n} (Prefers? a b) ¬all-aPb 
... | any-bRa = Any.map (λ x v-aPb _ → x v-aPb) any-bRa


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
  

aDb→aDc : {v : Voter} → (election : SocialPreference {n}) → (Decisive a b election v) → (Decisive a c election v)
aDb→aDc {a = a} {b = b} {c = c} e aDb v-aPc with Prefers? a c (SocialPreference.SocialPreferenceFunction e) 
... | false because ofⁿ ¬p = {!   !}
... | true because ofʸ p = p

arrows-theorem : (election : SocialPreference {n}) → Any (Dictator {n} {m} election) (SocialPreference.Ballots election)
arrows-theorem e = {!   !}