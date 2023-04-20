module CategoryTheory.01-Categories.5-Isomorphisms where

open import Algebra using (Group)
open import Algebra.Morphism using (module GroupMorphisms)
import Algebra.Morphism.Construct.Composition as AlgMorComp
import Algebra.Morphism.Construct.Identity as AlgMorId
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁)
open import Data.Unit using (⊤; tt)
open import Function as Fun using (flip; _$_; _on_; _↔_; Inverse)
import Function.Construct.Composition as FunComp
import Function.Construct.Identity as FunId
import Function.Construct.Symmetry as FunSym
import Function.Equality as FunEq
open import Level using (0ℓ; _⊔_; suc)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as RelIndTriv
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import CategoryTheory.01-Categories.3-DefinitionOfACategory
open import CategoryTheory.01-Categories.4-ExamplesOfCategories
  using (structuredSetCategory; Monoid→Category)

module Iso {ℓo ℓa ℓ≈ₐ} (C : Category ℓo ℓa ℓ≈ₐ) where

  open Category C

  module _ {A B : Obj} (f : A —→ B) where

    isInverse : (g : B —→ A) → Set ℓ≈ₐ
    isInverse g = g ∘ f ≈ₐ id A × f ∘ g ≈ₐ id B

    isIsomorphism : Set (ℓa ⊔ ℓ≈ₐ)
    isIsomorphism = Σ[ g ∈ B —→ A ] isInverse g

    inverse-unique : (g₁ g₂ : B —→ A) → isInverse g₁ → isInverse g₂ → g₁ ≈ₐ g₂
    inverse-unique g₁ g₂ (g₁-invˡ , g₁-invʳ) (g₂-invˡ , g₂-invʳ) = begin
      g₁            ≈˘⟨ unitʳ g₁ ⟩
      g₁ ∘ id B     ≈˘⟨ ∘-congˡ g₂-invʳ ⟩
      g₁ ∘ f ∘ g₂   ≈⟨ assoc g₁ f g₂ ⟩
      (g₁ ∘ f) ∘ g₂ ≈⟨ ∘-congʳ g₁-invˡ ⟩
      id A ∘ g₂     ≈⟨ unitˡ g₂ ⟩
      g₂            ∎
      where
      open ≈-Reasoning (B —→-setoid A)

  _≅_ : Rel Obj (ℓa ⊔ ℓ≈ₐ)
  A ≅ B = Σ[ f ∈ A —→ B ] isIsomorphism f

module _ {c ℓ} (G : Group c ℓ) where

  open Group G

  Group→Category : Category 0ℓ c ℓ
  Group→Category = Monoid→Category monoid

  module _ where

    open Category Group→Category

    Group→Category-iso : (g : tt —→ tt) → Iso.isIsomorphism Group→Category g
    Group→Category-iso g = g ⁻¹ , inverseˡ g , inverseʳ g

module _ {c ℓ} (X : Setoid c ℓ) where

  open Setoid X
  open Inverse
  open ≈-Reasoning X

  Aut : Group (c ⊔ ℓ) (c ⊔ ℓ)
  Aut = record
    { Carrier = Inverse X X
    ; _≈_ = →-setoid._≈_ on to
    ; _∙_ = flip FunComp.inverse
    ; ε = FunId.inverse X
    ; _⁻¹ = FunSym.inverse
    ; isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = record
              { refl = →-setoid.refl
              ; sym = →-setoid.sym
              ; trans = →-setoid.trans }
            ; ∙-cong = λ {G₁} {G₂} {F₁} {F₂} G₁≈G₂ F₁≈F₂ x → begin
              to G₁ (to F₁ x) ≈⟨ to-cong G₁ (F₁≈F₂ x) ⟩
              to G₁ (to F₂ x) ≈⟨ G₁≈G₂ (to F₂ x) ⟩
              to G₂ (to F₂ x) ∎ }
          ; assoc = λ F G H x → refl }
        ; identity = (λ F x → refl) , (λ F x → refl) }
      ; inverse = inverseʳ , inverseˡ
      ; ⁻¹-cong = λ {F} {G} F≈G x → begin
        from F x                 ≈˘⟨ from-cong F (inverseˡ G x) ⟩
        from F (to G (from G x)) ≈˘⟨ from-cong F (F≈G (from G x)) ⟩
        from F (to F (from G x)) ≈⟨ inverseʳ F (from G x) ⟩
        from G x                 ∎ } }
    where
    module →-setoid =
      Setoid (FunEq.≡-setoid Carrier (RelIndTriv.indexedSetoid X))

module Subgroup {c ℓ} (G : Group c ℓ) where

  open Group G

  record ClosedSubset p : Set (suc (c ⊔ p)) where
    field
      P : Carrier → Set p
      ε-closed : P ε
      ∙-closed : {g g′ : Carrier} → P g → P g′ → P (g ∙ g′)
      ⁻¹-closed : {g : Carrier} → P g → P (g ⁻¹)

  subgroup : ∀ {p} → ClosedSubset p → Group (c ⊔ p) ℓ
  subgroup closedSubset = record
    { Carrier = Σ[ g ∈ Carrier ] P g
    ; _≈_ = _≈_ on proj₁
    ; _∙_ = λ (g , Pg) (h , Ph) → g ∙ h , ∙-closed Pg Ph
    ; ε = ε , ε-closed
    ; _⁻¹ = λ (g , Pg) → g ⁻¹ , ⁻¹-closed Pg
    ; isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = record
              { refl = refl
              ; sym = sym
              ; trans = trans }
            ; ∙-cong = ∙-cong }
          ; assoc = λ (g , _) (h , _) (i , _) → assoc g h i }
        ; identity = (λ (g , _) → identityˡ g) , (λ (g , _) → identityʳ g) }
      ; inverse = (λ (g , _) → inverseˡ g) , (λ (g , _) → inverseʳ g)
      ; ⁻¹-cong = ⁻¹-cong } }
    where
    open ClosedSubset closedSubset

Groups : ∀ {c ℓ} → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Groups {c} {ℓ} = structuredSetCategory record
  { Obj = Group c ℓ
  ; _—→_ = λ G H →
    let module G = Group G
        module H = Group H
        open GroupMorphisms G.rawGroup H.rawGroup
    in  Σ[ f ∈ (G.Carrier → H.Carrier) ] IsGroupHomomorphism f
  ; obj-setoid = Group.setoid
  ; fun = proj₁
  ; ≈-homo = λ {G} {H} (_ , homo) →
    let open GroupMorphisms (Group.rawGroup G) (Group.rawGroup H)
    in  IsGroupHomomorphism.isRelHomomorphism homo
  ; _∘_ = λ {G} {H} {I} (g , g-homo) (f , f-homo) →
    g Fun.∘ f ,
    AlgMorComp.isGroupHomomorphism (Group.trans I) f-homo g-homo
  ; _∘-fun_ = λ g f → ≡.refl
  ; id = λ G →
    let module G = Group G
    in  Fun.id , AlgMorId.isGroupHomomorphism G.rawGroup G.refl
  ; id-fun = ≡.refl }

module _ {c} (G : Group c c) where

  open module G = Group G
  open Category (Groups {c} {c})
  open Iso (Groups {c} {c})
  open Subgroup (Aut G.setoid)
  open Inverse hiding (isInverse)
  open ≈-Reasoning G.setoid

  cayley : Σ[ Gb ∈ ClosedSubset c ] G ≅ subgroup Gb
  cayley = Gb , i , j , i-j-inverses
    where
    Gb = record
      { P = λ gb → Σ[ g ∈ Carrier ] ((h : Carrier) → to gb h ≈ g ∙ h)
      ; ε-closed = ε , sym Fun.∘ identityˡ
      ; ∙-closed = λ {g₁b} {g₂b} (g₁ , g₁bh≈g₁h) (g₂ , g₂bh≈g₂h) →
        (g₁ ∙ g₂) ,
        λ h → begin
          to g₁b (to g₂b h) ≈⟨ to-cong g₁b (g₂bh≈g₂h h) ⟩
          to g₁b (g₂ ∙ h)   ≈⟨ g₁bh≈g₁h (g₂ ∙ h) ⟩
          g₁ ∙ (g₂ ∙ h)     ≈˘⟨ G.assoc g₁ g₂ h ⟩
          g₁ ∙ g₂ ∙ h       ∎
      ; ⁻¹-closed = λ {gb} (g , gbh≈gh) →
        g ⁻¹ ,
        λ h → begin
          from gb h                  ≈˘⟨ from-cong gb (identityˡ h) ⟩
          from gb (ε ∙ h)            ≈˘⟨ from-cong gb (∙-congʳ (G.inverseʳ g)) ⟩
          from gb (g ∙ g ⁻¹ ∙ h)     ≈⟨ from-cong gb (G.assoc g (g ⁻¹) h) ⟩
          from gb (g ∙ (g ⁻¹ ∙ h))   ≈˘⟨ from-cong gb (gbh≈gh (g ⁻¹ ∙ h)) ⟩
          from gb (to gb (g ⁻¹ ∙ h)) ≈⟨ Inverse.inverseʳ gb (g ⁻¹ ∙ h) ⟩
          g ⁻¹ ∙ h                   ∎ }
    i : G —→ subgroup Gb
    i =
      (λ g →
        record
          { to = g ∙_
          ; from = g ⁻¹ ∙_
          ; to-cong = ∙-congˡ
          ; from-cong = ∙-congˡ
          ; inverse =
            (λ h → begin
              g ∙ (g ⁻¹ ∙ h) ≈˘⟨ G.assoc g (g ⁻¹) h ⟩
              g ∙ g ⁻¹ ∙ h   ≈⟨ ∙-congʳ (G.inverseʳ g) ⟩
              ε ∙ h          ≈⟨ identityˡ h ⟩
              h              ∎) ,
            (λ h → begin
              g ⁻¹ ∙ (g ∙ h) ≈˘⟨ G.assoc (g ⁻¹) g h ⟩
              g ⁻¹ ∙ g ∙ h   ≈⟨ ∙-congʳ (G.inverseˡ g) ⟩
              ε ∙ h          ≈⟨ identityˡ h ⟩
              h              ∎) } ,
        g , (λ h → refl)) ,
      record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = λ g₁≈g₂ h → ∙-congʳ g₁≈g₂ }
            ; homo = G.assoc }
          ; ε-homo = G.identityˡ }
        ; ⁻¹-homo = λ g h → refl }
    j : subgroup Gb —→ G
    j =
      (λ (gb , _) → to gb ε) ,
      record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = _$ ε }
            ; homo = λ (g₁b , g₁ , g₁bh≈g₁h) (g₂b , g₂ , g₂bh≈g₂h) → begin
              to g₁b (to g₂b ε)   ≈⟨ g₁bh≈g₁h (to g₂b ε) ⟩
              g₁ ∙ to g₂b ε       ≈˘⟨ ∙-congʳ (identityʳ g₁) ⟩
              (g₁ ∙ ε) ∙ to g₂b ε ≈˘⟨ ∙-congʳ (g₁bh≈g₁h ε) ⟩
              to g₁b ε ∙ to g₂b ε ∎ }
          ; ε-homo = refl }
        ; ⁻¹-homo = λ (gb , g , gbh≈gh) → begin
          from gb ε              ≈˘⟨ from-cong gb (G.inverseʳ g) ⟩
          from gb (g ∙ g ⁻¹)     ≈˘⟨ from-cong gb (gbh≈gh (g ⁻¹)) ⟩
          from gb (to gb (g ⁻¹)) ≈⟨ Inverse.inverseʳ gb (g ⁻¹) ⟩
          g ⁻¹                   ≈˘⟨ ⁻¹-cong (identityʳ g) ⟩
          (g ∙ ε) ⁻¹             ≈˘⟨ ⁻¹-cong (gbh≈gh ε) ⟩
          (to gb ε) ⁻¹           ∎ }
    i-j-inverses : isInverse {G} {subgroup Gb} i j
    i-j-inverses =
      identityʳ ,
      (λ (gb , g , gbh≈gh) h → begin
        to gb ε ∙ h ≈⟨ ∙-congʳ (gbh≈gh ε) ⟩
        g ∙ ε ∙ h   ≈⟨ ∙-congʳ (identityʳ g) ⟩
        g ∙ h       ≈˘⟨ gbh≈gh h ⟩
        to gb h     ∎)
