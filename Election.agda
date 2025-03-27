module Election where

open import Voter
open WeakPreference using (Preference)
open import Votes

open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Vec as Vec
open import Data.Bool as Bool
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)

private
    variable
        m n : ℕ
        n>2 : n ℕ.> 2
        a b c : Fin n
        _R_ : Fin n → Fin n → Set

-- SWF v a b represents a strict preference for a over b given a set of votes v
data SWF {m n : ℕ} {n>2 : n ℕ.> 2} (v : Votes n n>2 m) : Fin n → Fin n → Set₁ where
  Transitivity : (a b c : Fin n) 
               → SWF v a b 
               → SWF v b c 
               → SWF v a c
  BinaryIIA : (a b : Fin n)
            → (v1 : Votes n n>2 m)
            → Similar m a b (Zipped n>2 a b v v1)
            → SWF v1 a b
            → SWF v a b
  Pareto : (a b : Fin n)
         → ElectionAgrees v a b
         → SWF v a b 

-- since an SWF (or social welfare function) represents a strict preference,
-- we postulate that it is decidable and transitive but not complete
postulate SWF-trans : (v : Votes n n>2 m)
                    → (a b c : Fin n) 
                    → SWF v a b 
                    → SWF v b c 
                    → SWF v a c

postulate SWF-dec   : (v : Votes n n>2 m)
                    → (a b : Fin n) 
                    →   SWF v a b 
                    ⊎ ¬ SWF v a b