{-# OPTIONS --without-K --safe --cubical #-}

module test where

open import Agda.Primitive renaming (Set to Type)
open import Data.Nat using (ℕ; zero; suc)
open import Cubical.Foundations.Prelude

_+_ : ℕ -> ℕ ->  ℕ
zero + n    = n
(suc n) + m = suc (n + m)

record Monoid (M : Type) : Type where
  field
    ϵ : M
    _·_ : M -> M -> M
    idnₗ : {x : M} -> Path M (ϵ · x) x
    idnᵣ : {x : M} -> Path M (x · ϵ) x
    assoc : {x y z : M} -> Path M (x · (y · z)) ((x · y) · z)

natIdnᵣ : {n : ℕ} -> Path ℕ (n + zero) n
natIdnᵣ {zero} i = zero
natIdnᵣ {suc n} = cong suc (natIdnᵣ {n})

natAssoc : (x y z : ℕ) → Path ℕ (x + (y + z)) ((x + y) + z)
natAssoc zero y z = refl
natAssoc (suc x) y z = cong suc (natAssoc x y z)

natAdditiveMonoid : Monoid ℕ
natAdditiveMonoid = record
  { ϵ = zero
  ; _·_ = _+_
  ; idnₗ = refl
  ; idnᵣ = natIdnᵣ
  ; assoc = λ {x} {y} {z} -> natAssoc x y z
  }
