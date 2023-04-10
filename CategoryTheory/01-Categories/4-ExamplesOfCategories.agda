module CategoryTheory.01-Categories.4-ExamplesOfCategories where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; swap)
open import Data.Unit using (⊤; tt)
open import Function as Fun using (Morphism; flip; _on_; _↔_)
open import Level using (0ℓ)
open import Relation.Binary as Rel using (REL; _⇔_; Setoid; Poset)
open import Relation.Binary.Construct.Always using (Always)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.Morphism using (PosetHomomorphism)
import Relation.Binary.Morphism.Construct.Composition as RelMorComp
import Relation.Binary.Morphism.Construct.Identity as RelMorId
open import Relation.Binary.PropositionalEquality as ≡ using
  (_≡_; refl; _≗_; cong; sym; subst; _→-setoid_; module ≡-Reasoning)

open import CategoryTheory.01-Categories.3-DefinitionOfACategory

open Category

Sets : Category Set Morphism _≗_
Sets ._∘_ = Fun._∘′_
Sets .id A = Fun.id {A = A}
Sets .equiv A B = Setoid.isEquivalence (A →-setoid B)
Sets .∘-cong {x = g₁} {y = g₂} {u = f₁} {v = f₂} g₁≗g₂ f₁≗f₂ x = begin
  g₁ (f₁ x) ≡⟨ cong g₁ (f₁≗f₂ x) ⟩
  g₁ (f₂ x) ≡⟨ g₁≗g₂ (f₂ x) ⟩
  g₂ (f₂ x) ∎
  where
  open ≡-Reasoning
Sets .assoc f g h x = refl
Sets .unitˡ f x = refl
Sets .unitʳ f x = refl

Sets_fin : Category (Σ[ A ∈ Set ] ∃[ n ] A ↔ Fin n)
  (λ (A , _) (B , _) → A → B) _≗_
Sets_fin ._∘_ = _∘_ Sets
Sets_fin .id (A , _) = id Sets A
Sets_fin .equiv (A , _) (B , _) = equiv Sets A B
Sets_fin .∘-cong = ∘-cong Sets
Sets_fin .assoc = assoc Sets
Sets_fin .unitˡ = unitˡ Sets
Sets_fin .unitʳ = unitʳ Sets

module _ where

  private
    Pos-≈ₐ : {P Q : Poset 0ℓ 0ℓ 0ℓ} → Rel.Rel (PosetHomomorphism P Q) 0ℓ
    Pos-≈ₐ {P} {Q} F G = ∀ {x y} → x P.≈ y → F.⟦ x ⟧ Q.≈ G.⟦ y ⟧
      where
      module P = Poset P
      module Q = Poset Q
      module F = PosetHomomorphism F
      module G = PosetHomomorphism G

  Pos : Category (Poset 0ℓ 0ℓ 0ℓ) PosetHomomorphism Pos-≈ₐ
  Pos ._∘_ g f = RelMorComp.posetHomomorphism f g
  Pos .id = RelMorId.posetHomomorphism
  Pos .equiv P Q = record
    { refl = λ {F} → PosetHomomorphism.cong F
    ; sym = λ F≈ₐG x≈y → Q.sym (F≈ₐG (P.sym x≈y))
    ; trans = λ F≈ₐG G≈ₐH x≈y → Q.trans (F≈ₐG P.refl) (G≈ₐH x≈y) }
    where
    module P = Poset.Eq P
    module Q = Poset.Eq Q
  Pos .∘-cong G₁≈ₐG₂ F₁≈ₐF₂ = G₁≈ₐG₂ Fun.∘ F₁≈ₐF₂
  Pos .assoc F G H = H.cong Fun.∘ G.cong Fun.∘ F.cong
    where
    module F = PosetHomomorphism F
    module G = PosetHomomorphism G
    module H = PosetHomomorphism H
  Pos .unitˡ F = PosetHomomorphism.cong F
  Pos .unitʳ F = PosetHomomorphism.cong F

Rel : Category Set (λ A B → REL A B 0ℓ) _⇔_
Rel ._∘_ g f = f ; g
Rel .id A = _≡_
Rel .equiv A B = record
  { refl = Fun.id , Fun.id
  ; sym = swap
  ; trans = λ (R⇒S , S⇒R) (S⇒T , T⇒S) → S⇒T Fun.∘ R⇒S , S⇒R Fun.∘ T⇒S }
Rel .∘-cong (S₁⇒S₂ , S₂⇒S₁) (R₁⇒R₂ , R₂⇒R₁) =
  (λ (b , aR₁b , bS₁c) → b , R₁⇒R₂ aR₁b , S₁⇒S₂ bS₁c) ,
  (λ (b , aR₂b , bS₂c) → b , R₂⇒R₁ aR₂b , S₂⇒S₁ bS₂c)
Rel .assoc R S T =
  (λ (c , (b , aRb , bSc) , cTd) → b , aRb , (c , bSc , cTd)) ,
  (λ (b , aRb , (c , bSc , cTd)) → c , (b , aRb , bSc) , cTd)
Rel .unitˡ R =
  (λ {a} {b} (b′ , aRb′ , b′≡b) → subst (R a) b′≡b aRb′) ,
  (λ {a} {b} aRb → b , aRb , refl)
Rel .unitʳ R =
  (λ {a} {b} (a′ , a≡a′ , a′Rb) → subst (flip R b) (sym a≡a′) a′Rb) ,
  (λ {a} {b} aRb → a , refl , aRb)

𝟙 : Category ⊤ (λ _ _ → ⊤) _≡_
𝟙 ._∘_ _ _ = tt
𝟙 .id = Fun.id
𝟙 .equiv _ _ = ≡.isEquivalence
𝟙 .∘-cong _ _ = refl
𝟙 .assoc _ _ _ = refl
𝟙 .unitˡ _ = refl
𝟙 .unitʳ _ = refl
