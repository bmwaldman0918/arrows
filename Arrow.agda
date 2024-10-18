open import Setup using (Voter; SocialPreference; Decisive; Prefers?; Prefers; Preference; P→R)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList; _∷_)
open import Data.List using (_∷_; List)
open import Data.List.Relation.Unary.All using (All; []; all?; uncons)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; satisfied)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Bool using (true; false)
open import Data.Empty
open import ListUtil

module Arrow where

private
    variable
        Candidate : Set
        a b c : Candidate

∃VoterInAgreementWithElection : {election : SocialPreference {Candidate}} → Prefers a b (SocialPreference.SocialPreferenceFunction election) → Any (Prefers a b) (toList (SocialPreference.Ballots election))
∃VoterInAgreementWithElection {a = a} {b = b} {election = election} election-aPb with any? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | true because ofʸ any-aPb = any-aPb
... | false because ofⁿ ¬any-aPb = ⊥-elim (election-aPb (P→R {v = Voter.prefs (SocialPreference.SocialPreferenceFunction election)} 
                                                          ((SocialPreference.Unanimity election) b a {!  ¬AnyP→AllCP !})))

ExistsPivot : (election : SocialPreference {Candidate}) → Any (Decisive a b election) (toList (SocialPreference.Ballots election))
ExistsPivot {a = a} {b = b} election with any? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | false because ofⁿ ¬p = here (λ head-bRa _ → ¬p (here head-bRa))
... | true because ofʸ any-aPb with all? (Prefers? a b) (toList (SocialPreference.Ballots election)) 
... | true because ofʸ All-aPb = here (λ _ → SocialPreference.Unanimity election a b All-aPb)
ExistsPivot {a = a} {b = b} election | true because ofʸ any-aPb | false because ofⁿ ¬All-aPb with (Prefers? a b) (SocialPreference.SocialPreferenceFunction election) 
ExistsPivot {a = a} {b = b} election | _ | _ | true because ofʸ election-aPb = here (λ _ → election-aPb)
ExistsPivot {a = a} {b = b} election | true because ofʸ (here head-aPb) | false because ofⁿ ¬All-aPb | false because ofⁿ election-bRa = here (λ _ → {!   !})
ExistsPivot {a = a} {b = b} election | true because ofʸ (there any-aPb) | false because ofⁿ ¬All-aPb | false because ofⁿ election-bRa = there {!   !}
{-
arrows-theorem : (election : SocialPreference) → Any (dictator election) (toList (socialPreference.ballots election))
arrows-theorem e with (toList (socialPreference.ballots e))
... | x = {!   !}
-}          
--- step 2  