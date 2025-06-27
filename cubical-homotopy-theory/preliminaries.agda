{-# OPTIONS --without-K --safe --cubical #-}

-- NOTE: I somewhat tried to follow the structure of the Cubical Homotopy Theory book, however, their proofs and definitions
-- do not have synthetic homotopy theory in mind and so I am also getting ideas from the HoTT book.

-- Also, this module contains more than the first chapter from the CHT book, it also contains implicit assumptions to be used
-- throught the book

module preliminaries where

open import Agda.Primitive renaming (Set to Type)
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product using (_×_)
open import Function
open import Function.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base

-- Definition (Functoriality)
record Functor {ℓ} (F : Type ℓ -> Type ℓ) : Type (lsuc ℓ) where
  field
    fmap : {X Y : Type ℓ} -> (X -> Y) -> F X -> F Y
    funIdn : {X : Type ℓ} -> fmap {X} id ≡ id
    funComp : {X Y Z : Type ℓ} {f : X -> Y} {g : Y -> Z} -> fmap (g ∘ f) ≡ fmap g ∘ fmap f

-- Theorem (Mapping space out of the point is equivalent to the codomain)
typeToposIsWellPointed : {ℓ : Level} { X : Type ℓ } -> (⊤ -> X) ≡ X
typeToposIsWellPointed = isoToPath (iso (λ f -> f tt) (λ x -> λ _ -> x) (λ x -> refl) (λ f -> refl))

-- Definition (Interval space)
data 𝕀 : Type where
  𝕚0 : 𝕀
  𝕚1 : 𝕀
  seg : Path 𝕀 𝕚0 𝕚1
open 𝕀 public

-- Definition (Pointed space)
record Pointed {ℓ} : Type (lsuc ℓ) where
  constructor _∋₊_
  field 
    space : Type ℓ
    point : space
open Pointed public

-- Definition (Adjoining a disjoint basepoint)
data _₊ {ℓ} (X : Type ℓ) : Type ℓ where
  inSpace : X -> X ₊
  pt : X ₊

-- The following 3 definitions follow the style of HoTT
-- Definition 1.1.8 (Cone of a space)
data Cone {ℓ} (X : Type ℓ) : Type ℓ where
  vertex : Cone X
  base : X -> Cone X
  generatrix : (x : X) -> Path (Cone X) (base x) vertex

-- Definition 1.1.10 (Suspension of a space)
-- NOTE: This is HoTT's way of defining the suspension. And I do use it for defining the spheres
-- however, for pointed theorems a latter definition will be prefered
data Susp {ℓ} (X : Type ℓ) : Type ℓ where
  north : Susp X
  south : Susp X
  mer : (x : X) -> Path (Susp X) north south

-- Example 1.1.12 (Functoriality of suspensions)
suspIsFunctorial : {ℓ : Level} -> Functor {ℓ} Susp
suspIsFunctorial = record
  { fmap = λ f -> λ
    { north -> north 
    ; south -> south
    ; (mer x i) -> mer (f x) i
    }
  ; funIdn = funExt (λ
    { north -> refl
    ; south -> refl
    ; (mer x i) -> refl
    })
  ; funComp = funExt (λ
    { north -> refl
    ; south -> refl
    ; (mer x i) -> refl
    })
  }

-- Definition 1.1.13 (Wedge sum)
_⋁_ : (X Y : Pointed {lzero}) -> Pointed 
_⋁_  X₊@(X ∋₊ x₀) Y₊@(Y ∋₊ y₀) = Pushout (inclpt X₊) (inclpt Y₊) ∋₊ inl x₀
  where inclpt : (X : Pointed {lzero}) -> ⊤ -> space X
        inclpt (X ∋₊ x₀) = λ _ -> x₀

-- Definition (Cone of a function)
FCone : {ℓ : Level} {X Y : Type ℓ} (f : X -> Y) -> Pointed {ℓ}
FCone f = Pushout !⊤ f ∋₊ inl tt
  where !⊤ : {ℓ : Level} {X : Type ℓ} -> X -> ⊤
        !⊤ _ = tt

-- Definition 1.1.15 (Smash product)
_⋀_ : (X Y : Pointed {lzero}) -> Pointed
_⋀_ X₊@(X ∋₊ x₀) Y₊@(Y ∋₊ y₀) = FCone (smash {X₊} {Y₊})
  where smash : {X Y : Pointed {lzero}} -> space (X ⋁ Y) -> space X × space Y
        smash {X ∋₊ x₀} {Y ∋₊ y₀} (inl x) = x , y₀
        smash {X ∋₊ x₀} {Y ∋₊ y₀} (inr y) = x₀ , y
        smash {X ∋₊ x₀} {Y ∋₊ y₀} (push x i) = x₀ , y₀

-- Definition (Sphere)
data 𝕊¹ : Type where
  baseₛ₁ : 𝕊¹
  loopₛ₁ : baseₛ₁ ≡ baseₛ₁

𝕊¹₊ : Pointed
𝕊¹₊ = 𝕊¹ ∋₊ baseₛ₁

-- NOTE: This is just a nice repackage of Susp for what is to come
Σ₊ : (X : Pointed {lzero}) -> Pointed
Σ₊ X = 𝕊¹₊ ⋀ X

-- Definition (Pointed Map)
record Map {ℓ} (X Y : Pointed {ℓ}) : Type ℓ where
  field
    map : space X -> space Y
    ptCoe : Path (space Y) (map (point X)) (point Y)

-- Definition (Loop Space)
-- NOTE: This follows CHT's definition
Ω :  (X : Pointed) -> Pointed
Ω X = record { space = Map 𝕊¹₊ X; point = record { map = λ s -> point X; ptCoe = refl } }
    
-- Proposition (Loop-Suspension Adjunction)
loopSuspAdjunction : {X Y : Pointed} -> Map (Σ₊ X) Y ≡ Map X (Ω Y)
loopSuspAdjunction = isoToPath (iso loopSuspCurry {!!} {!!} {!!})
  where loopSuspCurry : {X Y : Pointed} -> Map (Σ₊ X) Y -> Map X (Ω Y)
        loopSuspCurry = λ (record { map = f; ptCoe = h }) -> record
          { map = λ x -> record
            { map = λ
              { baseₛ₁ -> f (inl tt)
              ; (loopₛ₁ i) -> {!!}
              }
            ; ptCoe = h
            }
          ; ptCoe = {!!}
          }

-- Definition (Weak Equivalence)
record _≅_ {ℓ} (X Y : Type ℓ) : Type (lsuc ℓ) where
  field
    weakequiv : {K : Type ℓ} -> (K -> X) ≡ (K -> Y)
