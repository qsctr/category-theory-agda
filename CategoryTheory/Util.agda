module CategoryTheory.Util where

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)

subst₂-type-and-value : ∀ {ℓa ℓs ℓr} → {A : Set ℓa} →
  (S : Rel A ℓs) → (R : {a b : A} → Rel (S a b) ℓr) →
  {a a′ b b′ : A} → {x y : S a b} → {x′ y′ : S a′ b′} →
  a ≡ a′ → b ≡ b′ → x ≅ x′ → y ≅ y′ → R {a} {b} x y → R {a′} {b′} x′ y′
subst₂-type-and-value _ _ ≡.refl ≡.refl ≅.refl ≅.refl p = p

cong-type-and-value : ∀ {ℓa ℓb ℓr ℓs} → {A : Set ℓa} → {B : Set ℓb} →
  (R : Rel A ℓr) → (S : Rel B ℓs) → (F : A → B) →
  (f : {a₁ a₂ : A} → R a₁ a₂ → S (F a₁) (F a₂)) →
  {a₁ a₁′ a₂ a₂′ : A} → {x : R a₁ a₂} → {x′ : R a₁′ a₂′} →
  a₁ ≡ a₁′ → a₂ ≡ a₂′ → x ≅ x′ → f x ≅ f x′
cong-type-and-value _ _ _ _ ≡.refl ≡.refl ≅.refl = ≅.refl
