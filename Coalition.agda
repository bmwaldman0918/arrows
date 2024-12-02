module Coalition where

open import Setup
open Election
open VoterBehavior
open SocialPreference
open Voter
open WeakPreference.Preference
open import Data.Nat as ℕ hiding (_≟_)
open import Data.List as List
open import Data.Vec as Vec
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?)
open import Data.List.Relation.Unary.All
open import Relation.Unary using (Pred; ∁; _⊆_; _∈_)
open import Data.Fin as Fin hiding (splitAt)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
    variable
        m n : ℕ --- numbers of ballots/number of candidates
        m>0 : m ℕ.> 0 --- at least ballot
        n>1 : n ℕ.> 1 --- at least two candidates
        x y z : Fin n
        y≠z : ¬(y ≡ z)
        x≠z : ¬(x ≡ z)
        x≠y : ¬(x ≡ y)
        all-ballots : Vec (Voter n n>1) m
        G : List (Voter n n>1)

Constitution : (m n : ℕ) → (n>1 : n ℕ.> 1) → Vec (Voter n n>1) m → Set₁
Constitution m n n>1 ballots = Voter n n>1

--- A coalition is a subset of ballots in an election
Coalition : Vec (Voter n n>1) m → List (Voter n n>1) → Set₁
Coalition e c = All (λ x → Any (λ y → y ≡ x) e) c

LocallyDecisive : Coalition all-ballots G
                → Constitution m n n>1 all-ballots
                → Fin n → Fin n 
                → Set₁
LocallyDecisive {G = G} coalition result x y 
                = All (Prefers x y) G
                → Prefers x y result

--- decisive over pair
--- decisive
--- weakly decisive
--- proof statement will be: exists decisive coalition of one voter


--- field expansion lemma

--- group contraction lemma