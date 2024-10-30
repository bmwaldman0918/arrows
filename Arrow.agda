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

module Arrow where

private
    variable
        Candidate : Set
        a b c : Candidate
        
postulate IndepdenceOfIrrelevantAlternatives : {e1 e2 : SocialPreference {Candidate}} → (VoterPreferences e1) ≡ (VoterPreferences e2) → 
            (Prefers a b) (SocialPreference.SocialPreferenceFunction e1) → (Prefers a b) (SocialPreference.SocialPreferenceFunction e2)

{-
¬Any-aPb→All-bRa : {lv : List Voter} → ¬ (Any (Prefers a b) lv) → All (weaklyPrefers b a)  lv
¬Any-aPb→All-bRa {a = a} {b = b} {lv} ¬Any-aPb with lv
... | List.[] = []
... | x ∷ xs with (Preference.R-dec (Voter.prefs x) {b} {a}) | all? (weaklyPrefers? b a) xs
... | inj₁ bRa | false because ofⁿ ¬All-aPb = ⊥-elim (¬All-aPb (¬Any-aPb→All-bRa λ any-xs-aPb → ¬Any-aPb (there any-xs-aPb)))
... | inj₁ bRa | true because ofʸ p = bRa All.∷ p
... | inj₂ aPb | _ = ⊥-elim (¬Any-aPb (here aPb))

∃VoterInAgreementWithElection : {election : SocialPreference {Candidate}} → Prefers a b (SocialPreference.SocialPreferenceFunction election) → Any (Prefers a b) (toList (SocialPreference.Ballots election))
∃VoterInAgreementWithElection {a = a} {b = b} {election = election} election-aPb with any? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | true because ofʸ any-aPb = any-aPb
... | false because ofⁿ ¬any-aPb = ⊥-elim (election-aPb  (SocialPreference.weakUnanimity election b a (¬Any-aPb→All-bRa ¬any-aPb)))
-}

ExistsPivot : (election : SocialPreference {Candidate}) → Any (Decisive a b election) (toList (SocialPreference.Ballots election))
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

aDb→aDc : {v : Voter} → (election : SocialPreference {Candidate}) → (Decisive a b election v) → (Decisive a c election v)
aDb→aDc {a = a} {b = b} {c = c} e aDb v-aPc with Prefers? a c (SocialPreference.SocialPreferenceFunction e) 
... | false because ofⁿ ¬p = {!   !}
... | true because ofʸ p = p

arrows-theorem : (election : SocialPreference {Candidate}) → Any (Dictator election) (toList (SocialPreference.Ballots election))
arrows-theorem e with (ExistsPivot e)  
... | pivot = Any.map (λ isPivot a b → {! !}) pivot