module CategoryTheory.01-Categories.3-DefinitionOfACategory where

open import Level using (_⊔_; suc)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_; IsEquivalence; Setoid)

record IsCategory {ℓo ℓa ℓ≈ₐ} (Obj : Set ℓo) (_—→_ : Obj → Obj → Set ℓa)
  (_≈ₐ_ : {A B : Obj} → Rel (A —→ B) ℓ≈ₐ)
  : Set (ℓo ⊔ ℓa ⊔ ℓ≈ₐ) where
  infixr 9 _∘_
  infix 0 _—→-equiv_
  field
    _∘_ : {A B C : Obj} → (B —→ C) → (A —→ B) → (A —→ C)
    id : (A : Obj) → (A —→ A)
    _—→-equiv_ : (A B : Obj) → IsEquivalence (_≈ₐ_ {A} {B})
    ∘-cong : {A B C : Obj} →
      _∘_ Preserves₂ (_≈ₐ_ {B} {C}) ⟶ (_≈ₐ_ {A} {B}) ⟶ (_≈ₐ_ {A} {C})
    assoc : {A B C D : Obj} → (h : C —→ D) → (g : B —→ C) → (f : A —→ B) →
      (h ∘ (g ∘ f)) ≈ₐ ((h ∘ g) ∘ f)
    unitˡ : {A B : Obj} → (f : A —→ B) → (id B ∘ f) ≈ₐ f
    unitʳ : {A B : Obj} → (f : A —→ B) → (f ∘ id A) ≈ₐ f

  _—→-setoid_ : (A B : Obj) → Setoid ℓa ℓ≈ₐ
  A —→-setoid B = record { isEquivalence = A —→-equiv B }

  dom : {A B : Obj} → (A —→ B) → Obj
  dom {A} {_} _ = A

  cod : {A B : Obj} → (A —→ B) → Obj
  cod {_} {B} _ = B

  ∘-congˡ : {A B C : Obj} → {f f′ : A —→ B} → {g : B —→ C} →
    f ≈ₐ f′ → (g ∘ f) ≈ₐ (g ∘ f′)
  ∘-congˡ {A} {B} {C} f≈ₐf′ = ∘-cong (IsEquivalence.refl (B —→-equiv C)) f≈ₐf′

  ∘-congʳ : {A B C : Obj} → {f : A —→ B} → {g g′ : B —→ C} →
    g ≈ₐ g′ → (g ∘ f) ≈ₐ (g′ ∘ f)
  ∘-congʳ {A} {B} {C} g≈ₐg′ = ∘-cong g≈ₐg′ (IsEquivalence.refl (A —→-equiv B))

record Category ℓo ℓa ℓ≈ₐ : Set (suc (ℓo ⊔ ℓa ⊔ ℓ≈ₐ)) where
  infix 0 _—→_
  infix 4 _≈ₐ_
  field
    Obj : Set ℓo
    _—→_ : Obj → Obj → Set ℓa
    _≈ₐ_ : {A B : Obj} → Rel (A —→ B) ℓ≈ₐ
    isCategory : IsCategory Obj _—→_ _≈ₐ_

  open IsCategory isCategory public
