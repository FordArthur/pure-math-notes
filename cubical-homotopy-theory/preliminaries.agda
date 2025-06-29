{-# OPTIONS --without-K --safe --cubical #-}

-- NOTE: I somewhat tried to follow the structure of the Cubical Homotopy Theory book, however, their proofs and definitions
-- do not have synthetic homotopy theory in mind and so I am also getting ideas from the HoTT book.

-- Also, this module contains more than the first chapter from the CHT book, it also contains implicit assumptions to be used
-- throught the book

module preliminaries where

open import Agda.Primitive renaming (Set to Type)
open import Data.Unit
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
  constructor ℱ𝓊𝓃𝒸𝓉
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
suspIsFunctorial = ℱ𝓊𝓃𝒸𝓉
  (λ f -> λ {north -> north; south -> south; (mer x i) -> mer (f x) i})
  (funExt (λ {north -> refl; south -> refl; (mer x i) -> refl}))
  (funExt (λ {north -> refl; south -> refl; (mer x i) -> refl}))

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
Ω₁ : (X : Pointed {lzero}) -> Pointed
Ω₁ (X ∋₊ x₀) = x₀ ≡ x₀ ∋₊ refl

_Ω⁺_ : (n : ℕ) (X : Pointed {lzero}) -> Pointed
_Ω⁺_ zero X    = Ω₁ X
_Ω⁺_ (suc n) X = Ω₁ (n Ω⁺ X)

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
    curry₊ {Y = Y} (Map f h) = Map (λ x -> Map (λ y -> f (inr (x , y)))
                                       (sym (cong f (push (inl x))) ∙ h))
                           (cong₂ Map (funExt (λ y -> sym (cong f (push (inr y))) ∙ h))
                                      (λ i -> λ j -> {!h (i ∨ j)!})) -- in j: p p⁻¹ -> z₀ in i: f x₀ -> z₀

    uncurry₊ : {X Y Z : Pointed} -> ⨀ (X ->₊ Y ->₊ Z) -> ⨀ (X ⋀ Y ->₊ Z)
    uncurry₊ {X ∋₊ x₀} {Y ∋₊ y₀} (Map f h) = Map (λ { (inl tt) -> map (f x₀) y₀
                                ; (inr (x , y)) -> map (f x) y
                                ; (push (inl x) i) -> (cong (λ g -> map g y₀) h ∙ sym (ptCoe (f x))) i
                                ; (push (inr y) i) -> (cong (λ g -> map g y₀) h ∙ sym (cong (λ g -> map g y) h)) i
                                ; (push (push tt i) j) -> {!ptCoe (f x₀) i0!}
                                })
                             (ptCoe (f x₀))

-- Lemma (Loop space is equivalent to based mapping space from 𝕊¹)
Ω₁X≡𝕊¹->₊X : {X : Pointed} -> Ω₁ X ≡ 𝕊¹₊ ->₊ X
Ω₁X≡𝕊¹->₊X = cong₂ _∋₊_ {!!} {!!}
  where
    loopToMap : {X : Pointed} -> ⨀ (Ω₁ X ->₊ (𝕊¹₊ ->₊ X))
    loopToMap = Map ((λ l -> Map (λ { baseₛ₁ -> l i0; (loopₛ₁ i) -> l i}) refl))
                    (cong₂ Map (funExt (λ {baseₛ₁ -> refl; (loopₛ₁ i) -> λ j -> refl i j})) {!!})

    mapToLoop : {X : Pointed} -> ⨀ ((𝕊¹₊ ->₊ X) ->₊ Ω₁ X)
    mapToLoop = Map (λ (Map f h) -> sym h ∙ (cong f loopₛ₁) ∙ h)
                    (sym (cong (λ q -> q ∙ refl ∙ refl) symRefl) ∙ (sym (lUnit (refl ∙ refl))) ∙ (sym (rUnit refl)))

    -- loopMap∘mapLoop : {X : Pointed {lzero}} -> section (loopToMap {X}) mapToLoop
    -- loopMap∘mapLoop (Map f h) = cong₂ Map (funExt (λ {baseₛ₁ -> {!!}; (loopₛ₁ i) -> {!!}})) {!!}

    -- mapLoop∘loopMap : {X : Pointed {lzero}} -> retract (loopToMap {X}) mapToLoop
    -- mapLoop∘loopMap p = assoc (sym refl) p refl ∙ sym (rUnit ((sym refl) ∙ p)) ∙ sym (cong (λ q -> q ∙ p) symRefl) ∙ sym (lUnit p)
    
-- Lemma (Suspension is equivalent to smash prod. with 𝕊¹)
Σ₊X≡X⋀𝕊¹ : {X : Pointed} -> Σ₊ X ≡ X ⋀ 𝕊¹₊
Σ₊X≡X⋀𝕊¹ = cong₂ _∋₊_ (isoToPath (iso suspToSmash smashToSusp {!!} {!!})) {!!}
  where
    suspToSmash : {X : Pointed} -> ⨀ (Σ₊ X) -> ⨀ (X ⋀ 𝕊¹₊)
    suspToSmash = λ { north -> inl tt
                    ; south -> inl tt
                    ; (mer x i) -> (push (inl x) ∙ (λ j -> inr (x , loopₛ₁ j)) ∙ sym (push (inl x))) i
                    }

    smashToSusp : {X : Pointed} -> ⨀ (X ⋀ 𝕊¹₊) -> ⨀ (Σ₊ X) 
    smashToSusp {X ∋₊ x₀} = λ { (inl tt) -> north
                    ; (inr (x , baseₛ₁)) -> north
                    ; (inr (x , (loopₛ₁ i))) -> (mer x ∙ sym (mer x₀)) i
                    ; (push (inl x) i) -> refl i
                    ; (push (inr baseₛ₁) i) -> refl i
                    ; (push (inr (loopₛ₁ i)) j) -> sym (lCancel (sym (mer x₀))) j i
                    ; (push (push tt i) j) -> refl j i
                    }

-- Proposition (Loop-Suspension Adjunction)
loopSuspAdjunction : {X Y : Pointed} -> ⨀ (Σ₊ X ->₊ Y) ≡ ⨀ (X ->₊ Ω₁ Y)
loopSuspAdjunction {X} {Y} = cong (λ K -> Map₊ K Y) Σ₊X≡X⋀𝕊¹ ∙ exponentialLaw₊ ∙ cong (λ K -> Map₊ X K) (sym Ω₁X≡𝕊¹->₊X)

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
-- record Functor₊ {ℓ} (F : Pointed {ℓ} -> Pointed {ℓ}) : Type (lsuc ℓ) where
--   constructor ℱ𝓊𝓃𝒸𝓉₊
--   field
--     fmap₊ : {X Y : Pointed {ℓ}} -> ⨀ (X ->₊ Y) -> ⨀ (F X ->₊ F Y)
--     funIdn₊ : {X : Pointed {ℓ}} -> fmap₊ {X} id ≡ id
--     funComp₊ : {X Y Z : Pointed {ℓ}} {f : X -> Y} {g : Y -> Z} -> fmap₊ (g ∘ f) ≡ fmap₊ g ∘ fmap₊ f
-- 
-- Ω⁺IsFunctorial : {n : ℕ} -> Functor₊ (_Ω⁺_ n)
-- Ω⁺IsFunctorial = {!!}

_π_ : (n : ℕ) (X : Pointed {lzero}) -> Group {lzero}
_π_ zero X = 𝒢𝓇𝓅 (⨀ (Ω₁ X)) (_∙_) refl (sym ∘ lUnit) (sym ∘ rUnit) sym lCancel rCancel assoc
_π_ (suc n) X = 𝒢𝓇𝓅 (⨀ (n Ω⁺ X)) (λ x y → {!!}) {!!} {!!} {!!} {!!} {!!} {!!} {!!}

