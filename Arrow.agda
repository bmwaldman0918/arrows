open import Setup
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.NonEmpty.Base using (List⁺; toList)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction; contraposition)

module Arrow where

private
    postulate
        a b c : Candidate

exists-pivot : (election : socialPreference) → Any (decisive a b election) (toList (socialPreference.ballots election))
exists-pivot election with (socialPreference.ballots election) | (prefers? a b (socialPreference.socialPreferenceFunction election))
... | c | d = {! d !}

arrows-theorem : (election : socialPreference) → Any (dictator election) (toList (socialPreference.ballots election))
arrows-theorem e with (toList (socialPreference.ballots e))
... | x = {!   !}
   
--- step 2 