{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.DiffInt.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ + b₁
    y = a₁ + b₀

ℤ = (ℕ × ℕ) / rel

open import Cubical.Data.Nat.Literals public

instance
  fromNatDiffInt : HasFromNat ℤ
  fromNatDiffInt = record { Constraint = λ _ → Unit ; fromNat = λ n → [ n , 0 ] }

instance
  fromNegDiffInt : HasFromNeg ℤ
  fromNegDiffInt = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ 0 , n ] }
