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
open import ListUtil

module Arrow where

private
    variable
        Candidate : Set
        a b c : Candidate

¬Any-aPb→All-bRa : {lv : List Voter} → ¬ (Any (Prefers a b) lv) → All (weaklyPrefers b a)  lv
¬Any-aPb→All-bRa {a = a} {b = b} {lv} ¬Any-aPb with lv
... | List.[] = []
... | x ∷ xs with (Preference.R-dec (Voter.prefs x) {b} {a}) | all? (weaklyPrefers? b a) xs
... | inj₁ bRa | false because ofⁿ ¬All-aPb = ⊥-elim (¬All-aPb (¬Any-aPb→All-bRa λ any-xs-aPb → ¬Any-aPb (there any-xs-aPb) ))
... | inj₁ bRa | true because ofʸ p = bRa All.∷ p
... | inj₂ aPb | _ = ⊥-elim (¬Any-aPb (here aPb))

favorite : (v : Voter) → (a : Candidate) → Set
favorite {Candidate = Candidate} v a = forall (b : Candidate) → Prefers a b v

least-favorite : (v : Voter) → (a : Candidate) → Set
least-favorite {Candidate = Candidate} v a = forall (b : Candidate) → Prefers b a v

extreme : (a : Candidate) → (v : Voter) → Set
extreme a v = favorite v a ⊎ least-favorite v a

extremal-lemma : {election : SocialPreference {Candidate}} → All (extreme a) (toList (SocialPreference.Ballots election)) → extreme a (SocialPreference.SocialPreferenceFunction election)
extremal-lemma all-extreme-a = {!   !}
{-
∃VoterInAgreementWithElection : {election : SocialPreference {Candidate}} → Prefers a b (SocialPreference.SocialPreferenceFunction election) → Any (Prefers a b) (toList (SocialPreference.Ballots election))
∃VoterInAgreementWithElection {a = a} {b = b} {election = election} election-aPb with any? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | true because ofʸ any-aPb = any-aPb
... | false because ofⁿ ¬any-aPb = ⊥-elim (election-aPb  {!   !})

ExistsPivot : (election : SocialPreference {Candidate}) → Any (Decisive a b election) (toList (SocialPreference.Ballots election))
ExistsPivot {a = a} {b = b} election with any? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | false because ofⁿ ¬p = here (λ head-bRa _ → ¬p (here head-bRa))
... | true because ofʸ any-aPb with all? (Prefers? a b) (toList (SocialPreference.Ballots election)) 
... | true because ofʸ All-aPb = here (λ _ → SocialPreference.Unanimity election a b All-aPb)
ExistsPivot {a = a} {b = b} election | true because ofʸ any-aPb | false because ofⁿ ¬All-aPb with (Prefers? a b) (SocialPreference.SocialPreferenceFunction election) 
ExistsPivot {a = a} {b = b} election | _ | _ | true because ofʸ election-aPb = here (λ _ → election-aPb)
ExistsPivot {a = a} {b = b} election | true because ofʸ (here head-aPb) | false because ofⁿ ¬All-aPb | false because ofⁿ election-bRa = here (λ _ → {!   !})
ExistsPivot {a = a} {b = b} election | true because ofʸ (there any-aPb) | false because ofⁿ ¬All-aPb | false because ofⁿ election-bRa = there {!   !}

arrows-theorem : (election : SocialPreference) → Any (dictator election) (toList (socialPreference.ballots election))
arrows-theorem e with (toList (socialPreference.ballots e))
... | x = {!   !}
-}            
--- step 2      