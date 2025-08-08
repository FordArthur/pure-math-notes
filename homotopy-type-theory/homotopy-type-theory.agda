{-# OPTIONS --without-K --safe --cubical #-}

module homotopy-type-theory where

open import Agda.Primitive renaming (Set to Type)
open import Cubical.Foundations.Prelude

-- Exercise 2.1. Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.
_∙₁_ : {ℓ : Level} {A : Type ℓ} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
p ∙₁ q = J {!!} {!!} {!!}
