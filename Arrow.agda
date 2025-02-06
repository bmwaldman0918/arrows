module Arrow where

open import Voter
open import Votes
open import Election
open import Coalition
open import Decisive
open import Data.Nat as ℕ

private
  variable
    m n : ℕ
    n>1 : n ℕ.> 1

-- the coalition of the whole is decisive
LemmaOne : (v : Votes n n>1 m) → Decisive (CoalitionOfWhole m) v
LemmaOne = ?