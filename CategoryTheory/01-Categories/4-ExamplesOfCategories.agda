module CategoryTheory.01-Categories.4-ExamplesOfCategories where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; swap)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as ⊤ₚ
open import Function as Fun using (Morphism; flip; _on_; _↔_; _↩_; mk↩)
open import Level using (Level; 0ℓ; _⊔_; suc)
open import Level.Literals using (#_)
open import Relation.Binary as Rel
  using (REL; _⇔_; _=[_]⇒_; IsEquivalence; Setoid; Preorder; Poset)
open import Relation.Binary.Construct.Always as Always using (Always)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.HeterogeneousEquality as ≅
  using (_≅_; module ≅-Reasoning)
open import Relation.Binary.Morphism using (PosetHomomorphism; mkPosetHomo)
import Relation.Binary.Morphism.Construct.Composition as RelMorComp
import Relation.Binary.Morphism.Construct.Identity as RelMorId
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Relation.Nullary.Decidable as Dec

open import CategoryTheory.01-Categories.3-DefinitionOfACategory
open import CategoryTheory.Util

open IsCategory
open Category

Sets : Category (# 1) 0ℓ 0ℓ
Sets .Obj = Set
Sets ._—→_ = Morphism
Sets ._≈ₐ_ = _≗_
Sets .isCategory ._∘_ = Fun._∘′_
Sets .isCategory .id A = Fun.id {A = A}
Sets .isCategory ._—→-equiv_ A B = Setoid.isEquivalence (A ≡.→-setoid B)
Sets .isCategory .∘-cong {x = g₁} {y = g₂} {u = f₁} {v = f₂} g₁≗g₂ f₁≗f₂ x =
  begin
    g₁ (f₁ x) ≡⟨ ≡.cong g₁ (f₁≗f₂ x) ⟩
    g₁ (f₂ x) ≡⟨ g₁≗g₂ (f₂ x) ⟩
    g₂ (f₂ x)
  ∎
  where
  open ≡-Reasoning
Sets .isCategory .assoc f g h x = ≡.refl
Sets .isCategory .unitˡ f x = ≡.refl
Sets .isCategory .unitʳ f x = ≡.refl

module Sets = Category Sets

Sets-fin : Category (# 1) 0ℓ 0ℓ
Sets-fin .Obj = Σ[ A ∈ Set ] ∃[ n ] A ↔ Fin n
Sets-fin ._—→_ (A , _) (B , _) = A → B
Sets-fin ._≈ₐ_ = _≗_
Sets-fin .isCategory ._∘_ = Sets._∘_
Sets-fin .isCategory .id (A , _) = Sets.id A
Sets-fin .isCategory ._—→-equiv_ (A , _) (B , _) = A Sets.—→-equiv B
Sets-fin .isCategory .∘-cong = Sets.∘-cong
Sets-fin .isCategory .assoc = Sets.assoc
Sets-fin .isCategory .unitˡ = Sets.unitˡ
Sets-fin .isCategory .unitʳ = Sets.unitʳ

Pos : ∀ {c ℓ₁ ℓ₂} → Category (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) (c ⊔ ℓ₁ ⊔ ℓ₂) (c ⊔ ℓ₁)
Pos {c} {ℓ₁} {ℓ₂} .Obj = Poset c ℓ₁ ℓ₂
Pos ._—→_ = PosetHomomorphism
Pos ._≈ₐ_ {P} {Q} F G = ∀ x → F.⟦ x ⟧ Q.≈ G.⟦ x ⟧
  where
  module Q = Poset Q
  module F = PosetHomomorphism F
  module G = PosetHomomorphism G
Pos .isCategory ._∘_ g f = RelMorComp.posetHomomorphism f g
Pos .isCategory .id = RelMorId.posetHomomorphism
Pos .isCategory ._—→-equiv_ P Q = record
  { refl = λ {F} x → Q.refl
  ; sym = λ F≈ₐG x → Q.sym (F≈ₐG x)
  ; trans = λ F≈ₐG G≈ₐH x → Q.trans (F≈ₐG x) (G≈ₐH x) }
  where
  module Q = Poset.Eq Q
Pos .isCategory .∘-cong {A} {B} {C} {G₁} {G₂} {F₁} {F₂} G₁≈ₐG₂ F₁≈ₐF₂ x = begin
  G₁.⟦ F₁.⟦ x ⟧ ⟧ ≈⟨ G₁.cong (F₁≈ₐF₂ x) ⟩
  G₁.⟦ F₂.⟦ x ⟧ ⟧ ≈⟨ G₁≈ₐG₂ F₂.⟦ x ⟧ ⟩
  G₂.⟦ F₂.⟦ x ⟧ ⟧ ∎
  where
  open ≈-Reasoning (Poset.Eq.setoid C)
  module G₁ = PosetHomomorphism G₁
  module G₂ = PosetHomomorphism G₂
  module F₁ = PosetHomomorphism F₁
  module F₂ = PosetHomomorphism F₂
Pos .isCategory .assoc {A} F G H x = H.cong (G.cong (F.cong A.Eq.refl))
  where
  module A = Poset A
  module F = PosetHomomorphism F
  module G = PosetHomomorphism G
  module H = PosetHomomorphism H
Pos .isCategory .unitˡ {A} F x = PosetHomomorphism.cong F (Poset.Eq.refl A)
Pos .isCategory .unitʳ {A} F x = PosetHomomorphism.cong F (Poset.Eq.refl A)

Rel : Category (# 1) (# 1) 0ℓ
Rel .Obj = Set
Rel ._—→_ A B = REL A B 0ℓ
Rel ._≈ₐ_ = _⇔_
Rel .isCategory ._∘_ g f = f ; g
Rel .isCategory .id A = _≡_
Rel .isCategory ._—→-equiv_ A B = record
  { refl = Fun.id , Fun.id
  ; sym = swap
  ; trans = λ (R⇒S , S⇒R) (S⇒T , T⇒S) → S⇒T Fun.∘ R⇒S , S⇒R Fun.∘ T⇒S }
Rel .isCategory .∘-cong (S₁⇒S₂ , S₂⇒S₁) (R₁⇒R₂ , R₂⇒R₁) =
  (λ (b , aR₁b , bS₁c) → b , R₁⇒R₂ aR₁b , S₁⇒S₂ bS₁c) ,
  (λ (b , aR₂b , bS₂c) → b , R₂⇒R₁ aR₂b , S₂⇒S₁ bS₂c)
Rel .isCategory .assoc R S T =
  (λ (c , (b , aRb , bSc) , cTd) → b , aRb , (c , bSc , cTd)) ,
  (λ (b , aRb , (c , bSc , cTd)) → c , (b , aRb , bSc) , cTd)
Rel .isCategory .unitˡ R =
  (λ {a} {b} (b′ , aRb′ , b′≡b) → ≡.subst (R a) b′≡b aRb′) ,
  (λ {a} {b} aRb → b , aRb , ≡.refl)
Rel .isCategory .unitʳ R =
  (λ {a} {b} (a′ , a≡a′ , a′Rb) → ≡.subst (flip R b) (≡.sym a≡a′) a′Rb) ,
  (λ {a} {b} aRb → a , ≡.refl , aRb)

𝟙 : Category 0ℓ 0ℓ 0ℓ
𝟙 .Obj = ⊤
𝟙 ._—→_ _ _ = ⊤
𝟙 ._≈ₐ_ = _≡_
𝟙 .isCategory ._∘_ _ _ = tt
𝟙 .isCategory .id tt = tt
𝟙 .isCategory ._—→-equiv_ _ _ = ≡.isEquivalence
𝟙 .isCategory .∘-cong _ _ = ≡.refl
𝟙 .isCategory .assoc _ _ _ = ≡.refl
𝟙 .isCategory .unitˡ _ = ≡.refl
𝟙 .isCategory .unitʳ _ = ≡.refl

module 𝟚 where

  data 𝟚-Obj : Set where
    ∗ ★ : 𝟚-Obj

  𝟚 : Category 0ℓ 0ℓ 0ℓ
  𝟚 .Obj = 𝟚-Obj
  𝟚 ._—→_ ∗ _ = ⊤
  𝟚 ._—→_ ★ ∗ = ⊥
  𝟚 ._—→_ ★ ★ = ⊤
  𝟚 ._≈ₐ_ = _≡_
  𝟚 .isCategory ._∘_ {∗} {_} {_} _ _ = tt
  𝟚 .isCategory ._∘_ {★} {∗} {∗} _ ff = ff
  𝟚 .isCategory ._∘_ {★} {★} {∗} ff _ = ff
  𝟚 .isCategory ._∘_ {★} {∗} {★} _ _ = tt
  𝟚 .isCategory ._∘_ {★} {★} {★} _ _ = tt
  𝟚 .isCategory .id ∗ = tt
  𝟚 .isCategory .id ★ = tt
  𝟚 .isCategory ._—→-equiv_ _ _ = ≡.isEquivalence
  𝟚 .isCategory .∘-cong {∗} {_} {_} _ _ = ≡.refl
  𝟚 .isCategory .∘-cong {★} {_} {∗} _ _ = ≡.refl
  𝟚 .isCategory .∘-cong {★} {_} {★} _ _ = ≡.refl
  𝟚 .isCategory .assoc {∗} {_} {_} {_} _ _ _ = ≡.refl
  𝟚 .isCategory .assoc {★} {_} {_} {∗} _ _ _ = ≡.refl
  𝟚 .isCategory .assoc {★} {_} {_} {★} _ _ _ = ≡.refl
  𝟚 .isCategory .unitˡ {∗} {_} _ = ≡.refl
  𝟚 .isCategory .unitˡ {★} {∗} _ = ≡.refl
  𝟚 .isCategory .unitˡ {★} {★} _ = ≡.refl
  𝟚 .isCategory .unitʳ {∗} {_} _ = ≡.refl
  𝟚 .isCategory .unitʳ {★} {∗} _ = ≡.refl
  𝟚 .isCategory .unitʳ {★} {★} _ = ≡.refl

  open Category 𝟚 public

open 𝟚 public using (𝟚)

module 𝟛 where

  data 𝟛-Obj : Set where
    ∗ ★ ● : 𝟛-Obj

  𝟛 : Category 0ℓ 0ℓ 0ℓ
  𝟛 .Obj = 𝟛-Obj
  𝟛 ._—→_ ∗ _ = ⊤
  𝟛 ._—→_ ★ ★ = ⊤
  𝟛 ._—→_ ★ ● = ⊤
  𝟛 ._—→_ ★ ∗ = ⊥
  𝟛 ._—→_ ● ● = ⊤
  𝟛 ._—→_ ● ∗ = ⊥
  𝟛 ._—→_ ● ★ = ⊥
  𝟛 ._≈ₐ_ = _≡_
  𝟛 .isCategory ._∘_ {∗} {_} {_} _ _ = tt
  𝟛 .isCategory ._∘_ {★} {_} {★} _ _ = tt
  𝟛 .isCategory ._∘_ {★} {_} {●} _ _ = tt
  𝟛 .isCategory ._∘_ {★} {∗} {∗} _ ff = ff
  𝟛 .isCategory ._∘_ {★} {★} {∗} ff _ = ff
  𝟛 .isCategory ._∘_ {★} {●} {∗} ff _ = ff
  𝟛 .isCategory ._∘_ {●} {_} {●} _ _ = tt
  𝟛 .isCategory ._∘_ {●} {∗} {∗} _ ff = ff
  𝟛 .isCategory ._∘_ {●} {★} {∗} ff _ = ff
  𝟛 .isCategory ._∘_ {●} {●} {∗} ff _ = ff
  𝟛 .isCategory ._∘_ {●} {∗} {★} _ ff = ff
  𝟛 .isCategory ._∘_ {●} {★} {★} _ ff = ff
  𝟛 .isCategory ._∘_ {●} {●} {★} ff _ = ff
  𝟛 .isCategory .id ∗ = tt
  𝟛 .isCategory .id ★ = tt
  𝟛 .isCategory .id ● = tt
  𝟛 .isCategory ._—→-equiv_ _ _ = ≡.isEquivalence
  𝟛 .isCategory .∘-cong {∗} {_} {_} _ _ = ≡.refl
  𝟛 .isCategory .∘-cong {★} {_} {∗} _ _ = ≡.refl
  𝟛 .isCategory .∘-cong {★} {_} {★} _ _ = ≡.refl
  𝟛 .isCategory .∘-cong {★} {_} {●} _ _ = ≡.refl
  𝟛 .isCategory .∘-cong {●} {_} {∗} _ _ = ≡.refl
  𝟛 .isCategory .∘-cong {●} {_} {★} _ _ = ≡.refl
  𝟛 .isCategory .∘-cong {●} {_} {●} _ _ = ≡.refl
  𝟛 .isCategory .assoc {∗} {_} {_} {_} _ _ _ = ≡.refl
  𝟛 .isCategory .assoc {★} {_} {_} {∗} _ _ _ = ≡.refl
  𝟛 .isCategory .assoc {★} {_} {_} {★} _ _ _ = ≡.refl
  𝟛 .isCategory .assoc {★} {_} {_} {●} _ _ _ = ≡.refl
  𝟛 .isCategory .assoc {●} {_} {_} {∗} _ _ _ = ≡.refl
  𝟛 .isCategory .assoc {●} {_} {_} {★} _ _ _ = ≡.refl
  𝟛 .isCategory .assoc {●} {_} {_} {●} _ _ _ = ≡.refl
  𝟛 .isCategory .unitˡ {∗} {_} _ = ≡.refl
  𝟛 .isCategory .unitˡ {★} {∗} _ = ≡.refl
  𝟛 .isCategory .unitˡ {★} {★} _ = ≡.refl
  𝟛 .isCategory .unitˡ {★} {●} _ = ≡.refl
  𝟛 .isCategory .unitˡ {●} {∗} _ = ≡.refl
  𝟛 .isCategory .unitˡ {●} {★} _ = ≡.refl
  𝟛 .isCategory .unitˡ {●} {●} _ = ≡.refl
  𝟛 .isCategory .unitʳ {∗} {_} _ = ≡.refl
  𝟛 .isCategory .unitʳ {★} {∗} _ = ≡.refl
  𝟛 .isCategory .unitʳ {★} {★} _ = ≡.refl
  𝟛 .isCategory .unitʳ {★} {●} _ = ≡.refl
  𝟛 .isCategory .unitʳ {●} {∗} _ = ≡.refl
  𝟛 .isCategory .unitʳ {●} {★} _ = ≡.refl
  𝟛 .isCategory .unitʳ {●} {●} _ = ≡.refl

  open Category 𝟛 public

open 𝟛 public using (𝟛)

𝟘 : Category 0ℓ 0ℓ 0ℓ
𝟘 .Obj = ⊥
𝟘 ._—→_ _ _ = ⊤
𝟘 ._≈ₐ_ = _≡_
𝟘 .isCategory ._∘_ _ _ = tt
𝟘 .isCategory .id _ = tt
𝟘 .isCategory ._—→-equiv_ _ _ = ≡.isEquivalence
𝟘 .isCategory .∘-cong _ _ = ≡.refl
𝟘 .isCategory .assoc _ _ _ = ≡.refl
𝟘 .isCategory .unitˡ _ = ≡.refl
𝟘 .isCategory .unitʳ _ = ≡.refl

record IsFunctor {ℓoC ℓaC ℓ≈ₐC ℓoD ℓaD ℓ≈ₐD}
  {ObjC : Set ℓoC} {_—→C_ : ObjC → ObjC → Set ℓaC}
  {_≈ₐC_ : {A B : ObjC} → Rel.Rel (A —→C B) ℓ≈ₐC}
  {ObjD : Set ℓoD} {_—→D_ : ObjD → ObjD → Set ℓaD}
  {_≈ₐD_ : {A B : ObjD} → Rel.Rel (A —→D B) ℓ≈ₐD}
  (C : IsCategory ObjC _—→C_ _≈ₐC_) (D : IsCategory ObjD _—→D_ _≈ₐD_)
  (Fₒ : ObjC → ObjD) (Fₐ : {A B : ObjC} → (A —→C B) → (Fₒ A —→D Fₒ B))
  : Set (ℓoC ⊔ ℓaC ⊔ ℓ≈ₐC ⊔ ℓoD ⊔ ℓaD ⊔ ℓ≈ₐD) where
  private
    module C = IsCategory C
    module D = IsCategory D
  field
    Fₐ-cong : {A B : ObjC} → _≈ₐC_ {A} {B} =[ Fₐ ]⇒ _≈ₐD_
    F₁ : {A : ObjC} → Fₐ (C.id A) ≈ₐD D.id (Fₒ A)
    F∘ : {A A′ A′′ : ObjC} → (f : A —→C A′) → (g : A′ —→C A′′) →
      Fₐ (g C.∘ f) ≈ₐD (Fₐ g D.∘ Fₐ f)

record Functor {ℓoC ℓaC ℓ≈ₐC ℓoD ℓaD ℓ≈ₐD}
  (C : Category ℓoC ℓaC ℓ≈ₐC) (D : Category ℓoD ℓaD ℓ≈ₐD)
  : Set (suc (ℓoC ⊔ ℓaC ⊔ ℓ≈ₐC ⊔ ℓoD ⊔ ℓaD ⊔ ℓ≈ₐD)) where
  private
    module C = Category C
    module D = Category D
  field
    Fₒ : C.Obj → D.Obj
    Fₐ : {A B : C.Obj} → (A C.—→ B) → (Fₒ A D.—→ Fₒ B)
    isFunctor : IsFunctor C.isCategory D.isCategory Fₒ Fₐ

  open IsFunctor isFunctor public

module Cat where

  module _ {C D : Category 0ℓ 0ℓ 0ℓ} (F G : Functor C D) where

    private
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G

    module _ (Fₒ≗Gₒ : F.Fₒ ≗ G.Fₒ) {A B : C.Obj} where

      rewrite-dom-cod : (F.Fₒ A D.—→ F.Fₒ B) → (G.Fₒ A D.—→ G.Fₒ B)
      rewrite-dom-cod f rewrite Fₒ≗Gₒ A | Fₒ≗Gₒ B = f

      rewrite-dom-cod-≅ : (f : F.Fₒ A D.—→ F.Fₒ B) → f ≅ rewrite-dom-cod f
      rewrite-dom-cod-≅ f rewrite Fₒ≗Gₒ A | Fₒ≗Gₒ B = ≅.refl

      rewrite-dom-cod-cong :
        D._≈ₐ_ {F.Fₒ A} {F.Fₒ B} =[ rewrite-dom-cod ]⇒ D._≈ₐ_ {G.Fₒ A} {G.Fₒ B}
      rewrite-dom-cod-cong {f} {g} = subst₂-type-and-value D._—→_ D._≈ₐ_
        (Fₒ≗Gₒ A) (Fₒ≗Gₒ B) (rewrite-dom-cod-≅ f) (rewrite-dom-cod-≅ g)

  Cat : Category (# 1) (# 1) 0ℓ
  Cat .Obj = Category 0ℓ 0ℓ 0ℓ
  Cat ._—→_ = Functor
  Cat ._≈ₐ_ {C} {D} F G = Σ[ Fₒ≗Gₒ ∈ F.Fₒ ≗ G.Fₒ ]
    ({A B : C.Obj} → (f : A C.—→ B) →
      rewrite-dom-cod F G Fₒ≗Gₒ (F.Fₐ f) D.≈ₐ G.Fₐ f)
    where
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  Cat .isCategory ._∘_ {C} {D} {E} G F = record
    { Fₒ = G.Fₒ Fun.∘ F.Fₒ
    ; Fₐ = G.Fₐ Fun.∘ F.Fₐ
    ; isFunctor = record
      { Fₐ-cong = G.Fₐ-cong Fun.∘ F.Fₐ-cong
      ; F₁ = λ {A} →
        let open ≈-Reasoning (G.Fₒ (F.Fₒ A) E.—→-setoid G.Fₒ (F.Fₒ A))
        in begin
          G.Fₐ (F.Fₐ (C.id A)) ≈⟨ G.Fₐ-cong F.F₁ ⟩
          G.Fₐ (D.id (F.Fₒ A)) ≈⟨ G.F₁ ⟩
          E.id (G.Fₒ (F.Fₒ A)) ∎
      ; F∘ = λ {A} {A′} {A′′} f g →
        let open ≈-Reasoning (G.Fₒ (F.Fₒ A) E.—→-setoid G.Fₒ (F.Fₒ A′′))
        in begin
          G.Fₐ (F.Fₐ (g C.∘ f))           ≈⟨ G.Fₐ-cong (F.F∘ f g) ⟩
          G.Fₐ (F.Fₐ g D.∘ F.Fₐ f)        ≈⟨ G.F∘ (F.Fₐ f) (F.Fₐ g) ⟩
          G.Fₐ (F.Fₐ g) E.∘ G.Fₐ (F.Fₐ f) ∎ } }
    where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G
  Cat .isCategory .id C = record
    { Fₒ = Fun.id
    ; Fₐ = Fun.id
    ; isFunctor = record
      { Fₐ-cong = Fun.id
      ; F₁ = λ {A} → IsEquivalence.refl (A C.—→-equiv A)
      ; F∘ = λ {A} {A′} {A′′} f g → IsEquivalence.refl (A C.—→-equiv A′′) } }
    where
    module C = Category C
  Cat .isCategory ._—→-equiv_ _ D = record
    { refl = λ {F} →
      let module F = Functor F
      in  (λ A → ≡.refl) ,
          λ {A} {B} f → IsEquivalence.refl (F.Fₒ A D.—→-equiv F.Fₒ B)
    ; sym = λ {F} {G} (Fₒ≗Gₒ , Fₐ≈ₐGₐ) →
      let module F = Functor F
          module G = Functor G
          Gₒ≗Fₒ = ≡.sym Fun.∘ Fₒ≗Gₒ
      in  Gₒ≗Fₒ ,
          λ {A} {B} f → IsEquivalence.sym (F.Fₒ A D.—→-equiv F.Fₒ B)
            (subst₂-type-and-value D._—→_ D._≈ₐ_ (Gₒ≗Fₒ A) (Gₒ≗Fₒ B)
              (≅.sym (rewrite-dom-cod-≅ F G Fₒ≗Gₒ (F.Fₐ f)))
              (rewrite-dom-cod-≅ G F (Gₒ≗Fₒ) (G.Fₐ f)) (Fₐ≈ₐGₐ f))
    ; trans = λ {F} {G} {H} (Fₒ≗Gₒ , Fₐ≈ₐGₐ) (Gₒ≗Hₒ , Gₐ≈ₐHₐ) →
      let open ≅-Reasoning
          module F = Functor F
          module G = Functor G
          module H = Functor H
          Fₒ≗Hₒ A = ≡.trans (Fₒ≗Gₒ A) (Gₒ≗Hₒ A)
      in  Fₒ≗Hₒ ,
          λ {A} {B} f → IsEquivalence.trans (H.Fₒ A D.—→-equiv H.Fₒ B)
            (subst₂-type-and-value D._—→_ D._≈ₐ_ (Gₒ≗Hₒ A) (Gₒ≗Hₒ B)
              (begin
                rewrite-dom-cod F G Fₒ≗Gₒ (F.Fₐ f)
              ≅˘⟨ rewrite-dom-cod-≅ F G Fₒ≗Gₒ (F.Fₐ f) ⟩
                F.Fₐ f
              ≅⟨ rewrite-dom-cod-≅ F H Fₒ≗Hₒ (F.Fₐ f) ⟩
                rewrite-dom-cod F H Fₒ≗Hₒ (F.Fₐ f)
              ∎)
              (rewrite-dom-cod-≅ G H Gₒ≗Hₒ (G.Fₐ f))
              (Fₐ≈ₐGₐ f))
            (Gₐ≈ₐHₐ f) }
    where
    module D = Category D
  Cat .isCategory .∘-cong {_} {D} {E} {G₁} {G₂} {F₁} {F₂}
    (G₁ₒ≗G₂ₒ , G₁ₐ≈ₐG₂ₐ) (F₁ₒ≗F₂ₒ , F₁ₐ≈ₐF₂ₐ) = G₁ₒF₁ₒ≗G₂ₒF₂ₒ ,
      λ {A} {B} f → ≅.subst (E._≈ₐ G₂F₂.Fₐ f)
        (let open ≅-Reasoning
         in begin
              rewrite-dom-cod G₁ G₂ G₁ₒ≗G₂ₒ
                (G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f)))
            ≅˘⟨ rewrite-dom-cod-≅ G₁ G₂ G₁ₒ≗G₂ₒ
                  (G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f))) ⟩
              G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f))
            ≅˘⟨ cong-type-and-value D._—→_ E._—→_ G₁.Fₒ G₁.Fₐ (F₁ₒ≗F₂ₒ A)
                  (F₁ₒ≗F₂ₒ B) (rewrite-dom-cod-≅ F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f)) ⟩
              G₁.Fₐ (F₁.Fₐ f)
            ≅⟨ rewrite-dom-cod-≅ G₁F₁ G₂F₂ G₁ₒF₁ₒ≗G₂ₒF₂ₒ (G₁.Fₐ (F₁.Fₐ f)) ⟩
              rewrite-dom-cod G₁F₁ G₂F₂ G₁ₒF₁ₒ≗G₂ₒF₂ₒ (G₁.Fₐ (F₁.Fₐ f))
            ∎)
        (let open ≈-Reasoning (G₂.Fₒ (F₂.Fₒ A) E.—→-setoid G₂.Fₒ (F₂.Fₒ B))
         in begin
              rewrite-dom-cod G₁ G₂ G₁ₒ≗G₂ₒ
                (G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f)))
            ≈⟨ rewrite-dom-cod-cong G₁ G₂ G₁ₒ≗G₂ₒ (G₁.Fₐ-cong (F₁ₐ≈ₐF₂ₐ f)) ⟩
              rewrite-dom-cod G₁ G₂ G₁ₒ≗G₂ₒ
                (G₁.Fₐ (F₂.Fₐ f))
            ≈⟨ G₁ₐ≈ₐG₂ₐ (F₂.Fₐ f) ⟩
              G₂.Fₐ (F₂.Fₐ f)
            ∎)
    where
    module D = Category D
    module E = Category E
    module G₁ = Functor G₁
    module G₂ = Functor G₂
    module F₁ = Functor F₁
    module F₂ = Functor F₂
    G₁F₁ = Cat .isCategory ._∘_ G₁ F₁
    G₂F₂ = Cat .isCategory ._∘_ G₂ F₂
    module G₂F₂ = Functor G₂F₂
    G₁ₒF₁ₒ≗G₂ₒF₂ₒ : G₁.Fₒ Fun.∘ F₁.Fₒ ≗ G₂.Fₒ Fun.∘ F₂.Fₒ
    G₁ₒF₁ₒ≗G₂ₒF₂ₒ A = begin
      G₁.Fₒ (F₁.Fₒ A) ≡⟨ ≡.cong G₁.Fₒ (F₁ₒ≗F₂ₒ A) ⟩
      G₁.Fₒ (F₂.Fₒ A) ≡⟨ G₁ₒ≗G₂ₒ (F₂.Fₒ A) ⟩
      G₂.Fₒ (F₂.Fₒ A) ∎
      where
      open ≡-Reasoning
  Cat .isCategory .assoc {_} {_} {_} {C₄} F G H = (λ A → ≡.refl) ,
    λ {A} {B} f →
      IsEquivalence.refl (H.Fₒ (G.Fₒ (F.Fₒ A)) C₄.—→-equiv H.Fₒ (G.Fₒ (F.Fₒ B)))
    where
    module C₄ = Category C₄
    module F = Functor F
    module G = Functor G
    module H = Functor H
  Cat .isCategory .unitˡ {_} {D} F = (λ A → ≡.refl) ,
    λ {A} {B} f → IsEquivalence.refl (F.Fₒ A D.—→-equiv F.Fₒ B)
    where
    module D = Category D
    module F = Functor F
  Cat .isCategory .unitʳ {_} {D} F = (λ A → ≡.refl) ,
    λ {A} {B} f → IsEquivalence.refl (F.Fₒ A D.—→-equiv F.Fₒ B)
    where
    module D = Category D
    module F = Functor F

  open Category Cat public

open Cat public using (Cat)

module _ {c ℓ₁ ℓ₂} (P : Preorder c ℓ₁ ℓ₂) where

  private
    module P = Preorder P

  Preorder→Category : Category c ℓ₂ 0ℓ
  Preorder→Category .Obj = P.Carrier
  Preorder→Category ._—→_ = P._∼_
  Preorder→Category ._≈ₐ_ = Always
  Preorder→Category .isCategory ._∘_ g f = P.trans f g
  Preorder→Category .isCategory .id a = P.refl
  Preorder→Category .isCategory ._—→-equiv_ _ _ = Always.isEquivalence _ _
  Preorder→Category .isCategory .∘-cong _ _ = ⊤ₚ.tt
  Preorder→Category .isCategory .assoc _ _ _ = ⊤ₚ.tt
  Preorder→Category .isCategory .unitˡ _ = ⊤ₚ.tt
  Preorder→Category .isCategory .unitʳ _ = ⊤ₚ.tt

module _ {ℓo ℓa ℓ≈ₐ} (C : Category ℓo ℓa ℓ≈ₐ) where

  private
    module C = Category C

  Category→Preorder : Preorder ℓo ℓo ℓa
  Category→Preorder = record
    { Carrier = C.Obj
    ; _≈_ = _≡_
    ; _∼_ = C._—→_
    ; isPreorder = record
      { isEquivalence = ≡.isEquivalence
      ; reflexive = λ { ≡.refl → C.id _ }
      ; trans = flip C._∘_ } }

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {P : Poset ℓ₁ ℓ₂ ℓ₃} {Q : Poset ℓ₄ ℓ₅ ℓ₆} where

  private
    module P = Poset P
    module Q = Poset Q

  PosetHomomorphism→Functor : PosetHomomorphism P Q →
    Functor (Preorder→Category P.preorder) (Preorder→Category Q.preorder)
  PosetHomomorphism→Functor F = record
    { Fₒ = F.⟦_⟧
    ; Fₐ = F.mono
    ; isFunctor = record
      { Fₐ-cong = Fun.id
      ; F₁ = ⊤ₚ.tt
      ; F∘ = λ _ _ → ⊤ₚ.tt } }
    where
    module F = PosetHomomorphism F

  Functor→PosetHomomorphism :
    Functor (Preorder→Category P.preorder) (Preorder→Category Q.preorder) →
    PosetHomomorphism P Q
  Functor→PosetHomomorphism F = mkPosetHomo P Q F.Fₒ F.Fₐ
    where
    module F = Functor F

  PosetHomomorphism↩Functor : PosetHomomorphism P Q ↩
    Functor (Preorder→Category P.preorder) (Preorder→Category Q.preorder)
  PosetHomomorphism↩Functor = mk↩
    {to = PosetHomomorphism→Functor} {from = Functor→PosetHomomorphism}
    λ F → ≡.refl
