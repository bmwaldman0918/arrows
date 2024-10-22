open import Setup using (Voter; SocialPreference; Decisive; Prefers?; Prefers; Preference; P→R; Dec-Prefers; weaklyPrefers; weaklyPrefers?)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList; _∷_)
open import Data.List using (_∷_; List)
open import Data.List.Relation.Unary.All using (All; []; all?; uncons; map)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; satisfied)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Bool using (true; false)
open import Data.Empty
open import Level using (zero; suc; _⊔_)
open import ListUtil

module Arrow where

private
    variable
        Candidate : Set
        a b c : Candidate

¬Any-aPb→All-bRa : {lv : List Voter} → ¬ (Any (Prefers a b) lv) → All (weaklyPrefers b a)  lv
¬Any-aPb→All-bRa = λ x → {! ¬AnyP→AllCP  ? ?  !}
{-
¬Any-aPb→All-bRa {a = a} {b = b} {lv} ¬Any-aPb with lv
... | List.[] = []
... | x ∷ xs with (Preference.R-dec (Voter.prefs x) {b} {a}) | all? (weaklyPrefers? b a) xs
... | inj₁ bRa | false because ofⁿ ¬All-aPb = ⊥-elim (¬All-aPb (¬Any-aPb→All-bRa λ any-xs-aPb → ¬Any-aPb (there any-xs-aPb)))
... | inj₁ bRa | true because ofʸ p = bRa All.∷ p
... | inj₂ aPb | _ = ⊥-elim (¬Any-aPb (here aPb))
-}
∃VoterInAgreementWithElection : {election : SocialPreference {Candidate}} → Prefers a b (SocialPreference.SocialPreferenceFunction election) → Any (Prefers a b) (toList (SocialPreference.Ballots election))
∃VoterInAgreementWithElection {a = a} {b = b} {election = election} election-aPb with any? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | true because ofʸ any-aPb = any-aPb
... | false because ofⁿ ¬any-aPb = ⊥-elim (election-aPb  (SocialPreference.Unanimity election b a (¬Any-aPb→All-bRa ¬any-aPb)))


ExistsPivot : (election : SocialPreference {Candidate}) → Any (Decisive a b election) (toList (SocialPreference.Ballots election))
ExistsPivot {a = a} {b = b} election with any? (Prefers? a b) (toList (SocialPreference.Ballots election)) | (Prefers? a b) (SocialPreference.SocialPreferenceFunction election)
... | false because ofⁿ ¬any-aPb | false because ofⁿ election-bRa = {!   !}
... | false because ofⁿ ¬any-aPb | true because ofʸ election-aPb = {!   !}
... | true because ofʸ any-aPb | false because ofⁿ election-bRa = {!   !}
... | true because ofʸ any-aPb | true because ofʸ election-aPb = {!   !}
{-
arrows-theorem : (election : SocialPreference) → Any (dictator election) (toList (socialPreference.ballots election))
arrows-theorem e with (toList (socialPreference.ballots e))
... | x = {!   !}
-}              
--- step 2      