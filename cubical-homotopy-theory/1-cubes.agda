{-# OPTIONS --without-K --safe --cubical #-}

module 1-cubes where

open import Agda.Primitive renaming (Set to Type)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Cubical.Foundations.Prelude

open import preliminaries

-- Definition 2.1.1 (Fibration)
-- At first glance, the following definition differs quite a bit from the book's definition. However, they are not that different, we simply map out of homotopies instead of the product
-- with an interval. It is easy to see that these are equivalent (This is just my intuition that this equivalent formulation will yield cleaner proofs, and it seems like so, see below)
-- TODO?: Perhaps formalize the fact that they are equivalent
record Fibration {ℓ} {X Y : Type ℓ} (p : X -> Y) : Type (lsuc ℓ) where
  field
    holift : {W : Type ℓ} {f g : W -> Y} (h : Path (W -> Y) f g) (f̂ : W -> X) {liftf̂ : Path (W -> Y) (p ∘ f̂) f} -> Σ (W -> X) (λ ĝ -> Path (W -> X) f̂ ĝ)

-- Prop 2.1.5 (Trivial Fibration)
-- The following theorem is a sanity check that we do not overcomplicate things by defining fibration as above:
theTrivialFibrationIsAFibration : {ℓ : Level} {X F : Type ℓ} -> Fibration {ℓ} {X × F} {X} proj₁
theTrivialFibrationIsAFibration = record
  { holift = λ {W} -> λ {f} -> λ {g} -> λ h -> λ f̂ -> λ {liftf̂} -> (λ w -> (g w , (proj₂ ∘ f̂) w)) , (λ i -> λ w -> ((liftf̂ ∙ h) i w , (proj₂ ∘ f̂) w))
  }

-- Prop 2.1.7 (Evaluation Map)
eval : {ℓ : Level} {X Y : Pointed {ℓ}} -> Map X Y -> space Y
eval {ℓ} {X} record {map = f; ptCoe = h} = f (point X)

-- theEvaluationMapIsAFibration : {X Y : Pointed} -> Fibration eval
-- theEvaluationMapIsAFibration = record
--   { holift = λ {W} -> λ {f} -> λ {g} -> λ h -> λ f̂ -> {!!}
--   }
