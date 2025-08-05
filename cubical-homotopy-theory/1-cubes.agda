{-# OPTIONS --without-K --safe --cubical #-}

module 1-cubes where 

open import Agda.Primitive renaming (Set to Type)
open import Function using (_∘_; _$_; _|>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

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
eval : {ℓ : Level} {X Y : Pointed ℓ} -> X →∙ Y -> fst Y
eval {ℓ} {X} f = fst f (snd X)

theEvaluationMapIsAFibration : {ℓ : Level} {X Y : Pointed ℓ} -> Fibration {ℓ} {X →∙ Y} eval
theEvaluationMapIsAFibration = record
  { holift = λ {W} -> λ {f} -> λ {g} -> λ h -> λ f̂ -> λ {liftf̂} -> (λ w -> (λ x -> g w) , sym (cong (_|>_ w) $ liftf̂ ∙ h) ∙ snd (f̂ w)) , {!!}
  }

-- This really should be in the preliminaries but for the time being:
PathSpace : {ℓ : Level} (X : Type ℓ) -> Type ℓ
PathSpace X = Σ[ (x₀ , x₁) ∈ X × X ] x₀ ≡ x₁

-- Definition 2.2.1 (Mapping space)
MapSpace : {ℓ : Level} {X Y : Type ℓ} -> (X -> Y) -> Type ℓ
MapSpace {ℓ} {X} {Y} f = Σ[ (x , α) ∈ X × PathSpace Y ] (f x ≡ fst (fst α))

-- Definition 2.2.1 (Homotopy fiber)
hofiber : {ℓ : Level} {X Y : Type ℓ} -> (X -> Y) -> Y -> Type ℓ
hofiber {ℓ} {X} {Y} f y = Σ[ x ∈ X ] (f x ≡ y)
