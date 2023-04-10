module CategoryTheory.01-Categories.3-DefinitionOfACategory where

open import Level using (_⊔_)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_; IsEquivalence)

record Category {ℓo} {ℓa} {ℓ≈} (Obj : Set ℓo) (_—→_ : Obj → Obj → Set ℓa)
  (_≈ₐ_ : {A B : Obj} → Rel (A —→ B) ℓ≈)
  : Set (ℓo ⊔ ℓa ⊔ ℓ≈) where
  field
    _∘_ : {A B C : Obj} → (B —→ C) → (A —→ B) → (A —→ C)
    id : (A : Obj) → (A —→ A)
    equiv : (A B : Obj) → IsEquivalence (_≈ₐ_ {A} {B})
    ∘-cong : {A B C : Obj} →
      _∘_ Preserves₂ (_≈ₐ_ {B} {C}) ⟶ (_≈ₐ_ {A} {B}) ⟶ (_≈ₐ_ {A} {C})
    assoc : {A B C D : Obj} → (f : A —→ B) → (g : B —→ C) → (h : C —→ D) →
      (h ∘ (g ∘ f)) ≈ₐ ((h ∘ g) ∘ f)
    unitˡ : {A B : Obj} → (f : A —→ B) → (id B ∘ f) ≈ₐ f
    unitʳ : {A B : Obj} → (f : A —→ B) → (f ∘ id A) ≈ₐ f

  dom : {A B : Obj} → (A —→ B) → Obj
  dom {A} {_} _ = A

  cod : {A B : Obj} → (A —→ B) → Obj
  cod {_} {B} _ = B
