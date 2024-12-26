module Coalition where

open import Data.Nat as ℕ hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool as Bool hiding (_≟_)
open import Data.List as List
open import Data.Vec as Vec
open import Data.Vec.Relation.Unary.Any as VecAny
open import Data.List.Relation.Unary.Any as ListAny
open import Data.List.Relation.Unary.All as ListAll
open import Data.Vec.Relation.Unary.All as VecAll
open import Relation.Unary as U using (Pred; ∁; _⊆_; _∈_)
open import Relation.Binary as B 
open import Data.Fin as Fin hiding (splitAt; _≟_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import FinFun

private
    variable
        m n : ℕ --- numbers of ballots/number of candidates
        m>0 : m ℕ.> 0 --- at least ballot
        n>1 : n ℕ.> 1 --- at least two candidates
        x y z : Fin n
        y≠z : ¬(y ≡ z)
        x≠z : ¬(x ≡ z)
        x≠y : ¬(x ≡ y)
        all-ballots altered-ballots : Vec (Voter n) m
        G : List (Voter n)

Constitution : (m n : ℕ) → (n>1 : n ℕ.> 1) → Vec (Voter n) m → Set
Constitution m n n>1 ballots = Fin n → Fin n → Bool

--- A coalition is a subset of ballots in an election
Coalition : Vec (Voter n) m → List (Voter n) → Set
Coalition e c = ListAll.All (λ x → VecAny.Any (λ y → y ≡ x) e) c

LocallyDecisive : (n>1 : n ℕ.> 1) → Coalition all-ballots G
                → Constitution m n n>1 all-ballots
                → Fin n → Fin n 
                → Set
LocallyDecisive {G = G} n>1 coalition Result x y 
                = (b : Bool) 
                → ListAll.All (λ v → v x y ≡ b) G 
                → Result x y ≡ b

Similar : (m : ℕ) → Fin n → Fin n → Vec (Voter n) m → Vec (Voter n) m → Set
Similar m x y orig alt = ∀ (i : Fin m) → (Vec.lookup orig i) x y ≡ (Vec.lookup alt i) x y

Similar? : (x y : Fin n) → (orig alt : Vec (Voter n) m) → Dec (Similar m x y orig alt)
Similar? x y [] [] = true because ofʸ (λ i → Eq.refl)
Similar? x y (h-orig ∷ orig) (h-alt ∷ alt) with (h-orig x y) Bool.≟ (h-alt x y)
... | false because ofⁿ ¬p = false because ofⁿ λ sim → ¬p (sim zero)
... | true because ofʸ p with Similar? x y orig alt
... | false because ofⁿ ¬p = false because ofⁿ λ sim → ¬p λ i → sim (raise (suc zero) i)
... | true because ofʸ p' = true because ofʸ λ {zero → p
                                              ; (suc i) → p' i}

postulate
  Transitivity : (e : Constitution m n n>1 all-ballots) 
               → (e x y) ≡ true
               → (e y z) ≡ true
               → (e x z) ≡ true
  ParetoEfficiency : (e : Constitution m n n>1 all-ballots)
                   → (b : Bool)
                   → VecAll.All (λ v → (v x y) ≡ b) all-ballots 
                   → (e x y) ≡ b
  IIA : (e : Constitution m n n>1 all-ballots)
      → (e' : Constitution m n n>1 altered-ballots)
      → (b : Bool)
      → (Similar m x y all-ballots altered-ballots)
      → (e  x y) ≡ b
      → (e' x y) ≡ b

Alter-Voter-For-FieldExpansion : Fin n → Fin n → Fin n → Voter n → List (Voter n) → Voter n
Alter-Voter-For-FieldExpansion x y z v G a b with Fin._≟_ a y | Fin._≟_ b z
... | true because _ | true because _ = true
... | _ | _ with ListAny.any? (λ v' → v ≟ v') G | Fin._≟_ a y | Fin._≟_ b z 
... | false because _ | true because _ | true because _ = true
... | false because _ | _ | _ = v a b
... | true because _ | true because _ | true because _ = false
... | true because _ | _ | _ = v a b

Altered-For-FieldExpansion : Fin n → Fin n → Fin n 
                    → (ballots : Vec (Voter n) m) 
                    → Coalition {n} ballots G
                    → Vec (Voter n) m
Altered-For-FieldExpansion {n = n} {G = G} x y z ballots c = helper x y z ballots where
  helper : Fin n → Fin n → Fin n 
         → (ballots : Vec (Voter n) m) 
         → Vec (Voter n) m
  helper x y z [] = []
  helper {n} x y z (v ∷ tail) = Alter-Voter-For-FieldExpansion x y z v G ∷ (helper x y z tail) 

--- this is basically my base case -- maybe altered voted needs to be a seperate type?
--- i don't know how to set up the contradiction
Altered-Voter-Similar : (x y z : Fin n)
                    → (v : Voter n)
                    → (l : List (Voter n))
                    → v x y ≡ (Alter-Voter-For-FieldExpansion x y z v l) x y
Altered-Voter-Similar x y z v l with v x y | (Alter-Voter-For-FieldExpansion x y z v l) x y
... | orig | alt = {!   !}

Altered-List-Similar : (c : Coalition all-ballots G) → 
        Similar m x y all-ballots (Altered-For-FieldExpansion x y z all-ballots c)
Altered-List-Similar {m = m} {all-ballots = all-ballots} {x = x} {y = y} {z = z} c 
    with (Altered-For-FieldExpansion x y z all-ballots c)
... | altered = λ {zero → {!   !}
           ; (suc i) → {!   !}}
{-
FieldExpansion : (e : Constitution m n n>1 all-ballots) 
               → (c : Coalition all-ballots G) 
               → LocallyDecisive n>1 c e x y 
               → LocallyDecisive n>1 c e x z
FieldExpansion {all-ballots = all-ballots} {x = x} {y = y} {z = z}
    e c ld b c-xz≡b with Altered-For-FieldExpansion x y z all-ballots c 
... | f = {!   !}
--- decisive over pair
--- decisive
--- weakly decisive
--- proof statement will be: exists decisive coalition of one voter

  
--- field expansion lemma
               
--- group contraction lemma 
-}