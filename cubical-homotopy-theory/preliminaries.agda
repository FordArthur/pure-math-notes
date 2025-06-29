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
open import Data.Product using (_×_; proj₁; proj₂; curry; uncurry)
open import Function
open import Function.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
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
    ⨀ : Type ℓ
    ✦ : ⨀
open Pointed public
infixr 1 _∋₊_

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
data Susp {ℓ} (X : Type ℓ) : Type ℓ where
  north : Susp X
  south : Susp X
  mer : X -> Path (Susp X) north south

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
  where inclpt : (X : Pointed {lzero}) -> ⊤ -> ⨀ X
        inclpt (X ∋₊ x₀) = λ _ -> x₀

-- Definition (Cone of a function)
FCone : {ℓ : Level} {X Y : Type ℓ} (f : X -> Y) -> Pointed {ℓ}
FCone f = Pushout !⊤ f ∋₊ inl tt
  where !⊤ : {ℓ : Level} {X : Type ℓ} -> X -> ⊤
        !⊤ _ = tt

-- Definition 1.1.15 (Smash product)
_⋀_ : (X Y : Pointed {lzero}) -> Pointed
_⋀_ X₊@(X ∋₊ x₀) Y₊@(Y ∋₊ y₀) = FCone (smash {X₊} {Y₊})
  where smash : {X Y : Pointed {lzero}} -> ⨀ (X ⋁ Y) -> ⨀ X × ⨀ Y
        smash {X ∋₊ x₀} {Y ∋₊ y₀} (inl x) = x , y₀
        smash {X ∋₊ x₀} {Y ∋₊ y₀} (inr y) = x₀ , y
        smash {X ∋₊ x₀} {Y ∋₊ y₀} (push _ i) = x₀ , y₀

-- Definition (Sphere)
data 𝕊¹ : Type where
  baseₛ₁ : 𝕊¹
  loopₛ₁ : baseₛ₁ ≡ baseₛ₁

𝕊¹₊ : Pointed
𝕊¹₊ = 𝕊¹ ∋₊ baseₛ₁

-- Definition 1.1.17 (Join)
_⋆_ : {ℓ : Level} (X Y : Type ℓ) -> Type ℓ
_⋆_ X Y = Pushout {A = X × Y} proj₁ proj₂

-- NOTE: This is just a nice repackage of Susp for what is to come
Σ₊ : (X : Pointed {lzero}) -> Pointed
Σ₊ X = Susp (⨀ X) ∋₊ north

-- Definition (Pointed Map)
record Map₊ {ℓ} (X Y : Pointed {ℓ}) : Type ℓ where
  constructor Map
  field
    map : ⨀ X -> ⨀ Y
    ptCoe : Path (⨀ Y) (map (✦ X)) (✦ Y)
open Map₊ public

infixr 10 _->₊_
_->₊_ : {ℓ : Level} (X Y : Pointed {ℓ}) -> Pointed {ℓ}
_->₊_ X₊ Y₊@(Y ∋₊ y₀) = Map₊ X₊ Y₊ ∋₊ Map (λ _ -> y₀) refl

-- Definition (Loop space)
Ω : (X : Pointed {lzero}) -> Pointed
Ω (X ∋₊ x₀) = x₀ ≡ x₀ ∋₊ refl

-- Definition (Free loop space)
L : (X : Type) -> Type
L X = 𝕊¹ -> X
    
-- Theorem 1.2.7 (Exponential law, unbased version)
exponentialLaw : {ℓ : Level} {X Y Z : Type ℓ} -> (X × Y -> Z) ≡ (X -> Y -> Z)
exponentialLaw = isoToPath (iso curry uncurry (λ f -> refl) (λ g -> refl))

-- Theorem 1.2.8 (Exponential law, based version)
exponentialLaw₊ : {X Y Z : Pointed} -> ⨀ (X ⋀ Y ->₊ Z) ≡ ⨀ (X ->₊ Y ->₊ Z)
exponentialLaw₊ = isoToPath (iso curry₊ uncurry₊ {!!} {!!})
  where
    curry₊ : {X Y Z : Pointed} -> ⨀ (X ⋀ Y ->₊ Z) -> ⨀ (X ->₊ Y ->₊ Z)
    curry₊ (Map f h) = Map (λ x -> Map (λ y -> f (inr (x , y)))
                                       (sym (cong f (push (inl x))) ∙ h))
                           (cong₂ Map (funExt (λ y -> sym (cong f (push (inr y))) ∙ h))
                                      {!!})

    uncurry₊ : {X Y Z : Pointed} -> ⨀ (X ->₊ Y ->₊ Z) -> ⨀ (X ⋀ Y ->₊ Z)
    uncurry₊ {X ∋₊ x₀} {Y ∋₊ y₀} (Map f h) = Map (λ { (inl tt) -> map (f x₀) y₀
                                ; (inr (x , y)) -> map (f x) y
                                ; (push (inl x) i) -> (cong (λ g -> map g y₀) h ∙ sym (ptCoe (f x))) i
                                ; (push (inr y) i) -> (cong (λ g -> map g y₀) h ∙ sym (cong (λ g -> map g y) h)) i
                                ; (push (push tt i) j) -> {!!}
                                })
                             (ptCoe (f x₀))

-- Proposition (Loop-Suspension Adjunction)
ΩX≡𝕊¹->₊X : {X : Pointed} -> ⨀ (Ω X) ≡ ⨀ (𝕊¹₊ ->₊ X)
ΩX≡𝕊¹->₊X = isoToPath (iso loopToMap mapToLoop loopMap∘mapLoop mapLoop∘loopMap)
  where
    loopToMap : {X : Pointed} -> ⨀ (Ω X) -> ⨀ (𝕊¹₊ ->₊ X)
    loopToMap l = Map (λ { baseₛ₁ -> l i0
                         ; (loopₛ₁ i) -> l i
                         })
                      refl

    mapToLoop : {X : Pointed} -> ⨀ (𝕊¹₊ ->₊ X) -> ⨀ (Ω X)
    mapToLoop (Map f h) = sym h ∙ (λ i -> f (loopₛ₁ i)) ∙ h

    loopMap∘mapLoop : {X : Pointed {lzero}} -> section (loopToMap {X}) mapToLoop
    loopMap∘mapLoop (Map f h) = cong₂ Map (funExt (λ { baseₛ₁ -> sym h; (loopₛ₁ i) -> {!!} })) {!!}

    mapLoop∘loopMap : {X : Pointed {lzero}} -> retract (loopToMap {X}) mapToLoop
    mapLoop∘loopMap p = {!!} -- sym (rUnit ((sym refl) ∙ p)) ∙ sym (cong (λ q -> q ∙ p) symRefl) ∙ sym (lUnit p)

Σ₊X≡X⋀𝕊¹ : {X : Pointed} -> ⨀ (Σ₊ X) ≡ ⨀ (X ⋀ 𝕊¹₊)
Σ₊X≡X⋀𝕊¹ = isoToPath (iso suspToSmash smashToSusp {!!} {!!})
  where
    suspToSmash : {X : Pointed} -> ⨀ (Σ₊ X) -> ⨀ (X ⋀ 𝕊¹₊)
    suspToSmash = λ { north -> inl tt
                    ; south -> inl tt
                    ; (mer x i) -> (push (inl x) ∙ (λ j -> inr (x , loopₛ₁ j)) ∙ sym (push (inl x))) i
                    }

    smashToSusp : {X : Pointed} -> ⨀ (X ⋀ 𝕊¹₊) -> ⨀ (Σ₊ X) 
    smashToSusp = λ { (inl tt) -> north
                    ; (inr (x , baseₛ₁)) -> mer x i0
                    ; (inr (x , (loopₛ₁ i))) -> north -- mer x i
                    ; (push x i) -> {!!}
                    }

-- loopSuspCurry : {X Y : Pointed} -> Σ₊ X ->₊ Y -> X ->₊ Ω Y
-- loopSuspCurry {X ∋₊ x₀} = λ (Map f h) -> Map
--   (λ x -> (sym h ∙ cong f (mer x)) ∙ sym (sym h ∙ cong f (mer x₀)))
--   (rCancel (sym h ∙ cong f (mer x₀)))
-- 
-- loopSuspUncurry : {X Y : Pointed} -> X ->₊ Ω Y -> Σ₊ X ->₊ Y
-- loopSuspUncurry {X ∋₊ x₀} = λ (Map f h) -> Map
--   (λ { north -> f x₀ i0
--      ; south -> f x₀ i1
--      ; (mer x i) -> f x i
--      })
--   refl
-- 
-- loopSuspSection : {X Y : Pointed} -> section loopSuspCurry loopSuspUncurry 
-- loopSuspSection = {!!}
-- 
-- loopSuspRetract : {X Y : Pointed} -> retract loopSuspCurry loopSuspUncurry 
-- loopSuspRetract = {!!}
-- 
-- loopSuspAdjunction : {X Y : Pointed} -> Σ₊ X ->₊ Y ≡ X ->₊ Ω Y
-- loopSuspAdjunction = isoToPath (iso loopSuspCurry loopSuspUncurry loopSuspSection loopSuspRetract)

-- Definition (Weak Equivalence)
_≅_ : {ℓ : Level} (X Y : Type ℓ) {K : Type ℓ} -> Type (lsuc ℓ)
_≅_ X Y {K} = (K -> X) ≡ (K -> Y)

-- Definition (Group)
record Group {ℓ} : Type (lsuc ℓ) where
  constructor 𝒢𝓇𝓅
  field 
    𝒢 : Type ℓ
    _✶_ : 𝒢 -> 𝒢 -> 𝒢
    ϵ : 𝒢
    𝒢-unitₗ : (x : 𝒢) -> ϵ ✶ x ≡ x
    𝒢-unitᵣ : (x : 𝒢) -> x ✶ ϵ ≡ x
    𝒢-inv : 𝒢 -> 𝒢
    𝒢-cancelₗ : (x : 𝒢) -> (𝒢-inv x) ✶ x ≡ ϵ
    𝒢-cancelᵣ : (x : 𝒢) -> x ✶ (𝒢-inv x) ≡ ϵ
    𝒢-assoc : (x y z : 𝒢) -> x ✶ (y ✶ z) ≡ (x ✶ y) ✶ z
open Group public

-- Definition (Nth homotopy group)
-- TODO: Generalize to make it actually nth
_π_ : (n : ℕ) (X : Pointed) -> Group
_π_ n X = 𝒢𝓇𝓅 (⨀ (Ω X)) (_∙_) refl (sym ∘ lUnit) (sym ∘ rUnit) sym lCancel rCancel assoc
