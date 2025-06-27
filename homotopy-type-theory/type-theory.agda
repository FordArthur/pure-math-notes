{-# OPTIONS --without-K --safe --cubical #-}

-- NOTE: This chapter is rather introductory, so it'll only contain the exercises

module type-theory where

open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Function using (_∘_)
open import Agda.Builtin.Sigma
open import Cubical.Foundations.Prelude

-- Exercise 1.1. Given functions f : A → B and g : B → C, define their composite g ◦ f : A → C. Show that we have h ◦ (g ◦ f) ≡ (h ◦ g) ◦ f.
_∘'_ : {ℓ : Level} {A B C : Type ℓ} -> (B -> C) -> (A -> B) -> A -> C
_∘'_ g f = λ a -> g (f a)

∘'-assoc : {ℓ : Level} {A B C D : Type ℓ} -> {h : C -> D} -> {g : B -> C} -> {f : A -> B} -> h ∘' (g ∘' f) ≡ (h ∘' g) ∘' f
∘'-assoc {h = h} {g = g} {f = f} = refl


-- Exercise 1.2. Derive the recursion principle for products recA×B using only the projections, and verify that the definitional equalities are valid. Do the same for Σ-types.
×-rec : {ℓ : Level} {A B C : Type ℓ} -> (A -> B -> C) -> (A × B) -> C
×-rec f = λ p -> f (proj₁ p) (proj₂ p)

Σ-rec : {ℓ : Level} {A : Type ℓ} {B : A -> Type ℓ} {C : Type ℓ} -> ((a : A) -> (b : B a) -> C) -> Σ A B -> C
Σ-rec f = λ p -> f (fst p) (snd p)

-- Exercise 1.3. Derive the induction principle for products indA×B, using only the projections and the propositional uniqueness principle uniqA×B. Verify that the definitional equalities are valid.
×-ind : {ℓ : Level} {A B : Type ℓ} {C : A × B -> Type ℓ} -> ((a : A) -> (b : B) -> C (a , b)) -> (p : A × B) -> C p
×-ind f = λ p -> f (proj₁ p) (proj₂ p)

Σ-ind : {ℓ : Level} {A : Type ℓ} {B : A -> Type ℓ} {C : Σ A B -> Type ℓ} -> ((a : A) -> (b : B a) -> C (a , b)) -> (p : Σ A B) -> C p
Σ-ind f = λ p -> f (fst p) (snd p)

-- Exercise 1.4. Assuming as given only the iterator for natural numbers iter : ∏ C:U C → (C → C) → N → C with the defining equations iter(C, c0, cs, 0) :≡ c0, iter(C, c0, cs, succ(n)) :≡ cs(iter(C, c0, cs, n)), derive a function having the type of the recursor recN. Show that the defining equations of the recursor hold propositionally for this function, using the induction principle for N.
iter : {ℓ : Level} {C : Type ℓ} -> C -> (C -> C) -> ℕ -> C
iter c₀ cₛ zero = c₀
iter c₀ cₛ (suc n) = cₛ (iter c₀ cₛ n)

ℕ-rec : {ℓ : Level} {C : Type ℓ} -> C -> (ℕ -> C -> C) -> ℕ -> C
ℕ-rec c₀ cₛ = proj₂ ∘ iter (zero , c₀) (λ (n , c) -> (n , cₛ n c))

zero-ℕ-rec : {ℓ : Level} {C : Type ℓ} {c₀ : C} {cₛ : ℕ -> C -> C} -> ℕ-rec c₀ cₛ zero ≡ c₀
zero-ℕ-rec = refl

suc-ℕ-rec : {ℓ : Level} {C : Type ℓ} {c₀ : C} {cₛ : ℕ -> C -> C} {n : ℕ} -> ℕ-rec c₀ cₛ (suc n) ≡ cₛ n (ℕ-rec c₀ cₛ n)
suc-ℕ-rec = {!!}

-- Exercise 1.5. Show that if we define A + B :≡ ∑(x:2) rec2(U , A, B, x), then we can give a definition of indA+B for which the definitional equalities stated in §1.7 hold.

Bool-rec : {ℓ : Level} {C : Type ℓ} -> C -> C -> Bool -> C
Bool-rec c₀ c₁ false = c₀
Bool-rec c₀ c₁ true = c₁

_+'_ : {ℓ : Level} (A B : Type ℓ) -> Type ℓ
_+'_ A B = Σ Bool (Bool-rec A B)

+'-ind : {ℓ : Level} {A B : Type ℓ} {C : A +' B -> Type ℓ} -> ((a : A) -> C (false , a)) -> ((b : B) -> C (true , b)) -> (p : A +' B) -> C p
+'-ind c₀ c₁ (false , a) = c₀ a
+'-ind c₀ c₁ (true , b) = c₁ b

-- inl-+'-ind : {ℓ : Level} {A B : Type ℓ} {C : A +' B -> Type ℓ} {a : A} {f₀ : (a' : A) -> C (false , a')} -> +'-ind ()
