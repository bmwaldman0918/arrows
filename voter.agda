open import Data.Nat as ℕ using (ℕ; _<_)
open import Relation.Binary using (Rel)
open import Level using (0ℓ; suc)
open import Data.List

record candidate : Set where
    field
        id : ℕ

record voter : Set₁ where
    constructor _,_
    field
        id : ℕ
        preferences : candidate → ℕ

prefsFunToRel : (candidate → ℕ) → Rel candidate 0ℓ
prefsFunToRel f x y = f x < f y


--- does R_i represent a function or an individual relation between two candidates
--- is the function stuff useful/important?
--- can i do everything with weak preference?
--- I don't think I need IIA/rank same but discuss
--- philosophical question -- should i be doing the relation stuff from scratch


--- type indicating two voters have the same relative prefs between two candidates
record socialPreferenceFunction (f : candidate → ℕ) : Set₁ where
    field
        --- if all voters prefer y to x, the social preference function prefers y to x
        unanimity : (x y : candidate) → (v : voter) → ((voter.preferences v x) < (voter.preferences v y)) → (f x < f y)