module Arrow where

open import Setup
open Election
open VoterBehavior
open SocialPreference
open ProfileIIIVoter

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; map; lookup;  _++_)
open import Data.Vec.Relation.Unary.All as All using (All; []; all?; uncons; map; _∷_)
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?; here; there; satisfied; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Bool using (true; false)
open import Data.Empty
open import VecUtil using (¬AllP→AnyCP)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Nat as ℕ using (ℕ; _>_)
open import Data.Fin hiding (splitAt)

private
    variable
        m n : ℕ --- numbers of ballots/number of candidates
        --- m>0 : m ℕ.> 0 --- at least ballot
        n>1 : n ℕ.> 1 --- at least two candidates
        a b c : Fin n
        
postulate 
    IndependenceOfIrrelevantAlternatives :  {e1 e2 : SocialPreference} 
        → VoterPreferences {m} {n} {n>1} e1 ≡ VoterPreferences {m} {n} {n>1} e2
        → Prefers {n} {n>1} a b (SocialPreferenceFunction e1) 
          -----------------------------------------
        → Prefers {n} {n>1} a b (SocialPreferenceFunction e2)

ExistsPivot : {m>0 : m ℕ.> 0}
            → (election : SocialPreference {m}) 
            -----------------------------------
            → Any (Decisive {m} {n} {n>1} a b election) (Ballots election)
ExistsPivot {m} {n} {n>1} {a} {b} election 
            with Prefers? {n} {n>1} a b (SocialPreferenceFunction election)
            | all? (Prefers? {n} {n>1} a b) (Ballots election)
ExistsPivot {m} {n} {n>1} {a} {b} {m>0} election 
          | false because ofⁿ ¬election-aPb
          | false because ofⁿ ¬all-aPb = Any.map (λ x y _ → x y) 
                                  (¬AllP→AnyCP {m} {m>0} (Prefers? {n} {n>1} a b) 
                                               λ all-aPb → ¬all-aPb all-aPb)
ExistsPivot {m} {n} {n>1} {a} {b} {m>0} election 
          | false because ofⁿ ¬election-aPb
          | true because ofʸ all-aPb 
          = ⊥-elim (¬election-aPb ((Unanimity election {n} {n>1}) a b (All.map (λ {aPb bRa → aPb bRa}) all-aPb)))
ExistsPivot {m = m} {n = n} {n>1 = n>1} {a = a} {b = b} election 
          | true because ofʸ election-aPb
          | _ with (Ballots election {n})
... | _ ∷ _ = here (λ _ election-bRa → election-aPb election-bRa)
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

ProfileIII-helper : {n>1 : n ℕ.> 1} → (b : Fin n) → Vec (Voter {n}) m → Vec (Voter {n}) m
ProfileIII-helper {n} {m} {n>1} b post-pivot = Vec.map (Voter→R2Voter {n} {n>1} b) post-pivot

ProfileIII : {n>1 : n ℕ.> 1} → (idx : Fin m) → (b : Fin n) → Vec (Voter {n}) m → Vec (Voter {n}) m
ProfileIII {n} {m} {n>1} zero b (x ∷ profileIV) = x ∷ ProfileIII-helper {n>1 = n>1} b profileIV
ProfileIII {n} {m} {n>1} (suc idx) b (x ∷ profileIV) = ((Voter→R2Voter {n>1 = n>1} b x) ∷ [])++(ProfileIII {n>1 = n>1} idx b profileIV)

aDb→aDc : {v : Voter} → (election : SocialPreference {m}) → (Decisive {m} {n} {n>1} a b election v) → (Decisive {m} {n} {n>1} a c election v)
aDb→aDc {n = n} {n>1 = n>1} {a = a} {b = b} {c = c} e aDb v-aPc with Prefers? {n} {n>1} a c (SocialPreferenceFunction e) 
... | false because ofⁿ ¬p = {!   !}
... | true because ofʸ p = p

{-
arrows-theorem : (election : SocialPreference {n}) → Any (Dictator {n} {m} election) (SocialPreference.Ballots election)
arrows-theorem e = {!   !}
-}