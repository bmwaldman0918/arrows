open import Setup using (Voter; SocialPreference; Decisive; Prefers?; Prefers; Preference)
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

--- notes
--- there must exist a pivot
--- either head prefers a to b
---

ExistsPivot : (election : SocialPreference {Candidate}) → Any (Decisive a b election) (toList (SocialPreference.Ballots election))
ExistsPivot {a = a} {b = b} election with 
              any? (Prefers? a b) (toList (SocialPreference.Ballots election))
            | all? (Prefers? a b) (toList (SocialPreference.Ballots election))
... | _                    | true because ofʸ p = here λ _ sp-bRa → 
                                          SocialPreference.Unanimity election a b p sp-bRa
... | false because ofⁿ ¬p | false because ofⁿ ¬p' = ⊥-elim (¬p {!   !})
... | true because ofʸ p   | _ with satisfied p 
... | fst , snd = here (λ head-bRa sp-bRa → {!   !})

{-
arrows-theorem : (election : SocialPreference) → Any (dictator election) (toList (socialPreference.ballots election))
arrows-theorem e with (toList (socialPreference.ballots e))
... | x = {!   !}
-}         
--- step 2 