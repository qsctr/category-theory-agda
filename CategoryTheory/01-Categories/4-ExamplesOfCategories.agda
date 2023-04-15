module CategoryTheory.01-Categories.4-ExamplesOfCategories where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; swap)
open import Data.Unit using (⊤; tt)
open import Function as Fun using (Morphism; flip; _on_; _↔_)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary as Rel
  using (REL; _⇔_; _=[_]⇒_; IsEquivalence; Setoid; Poset)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.HeterogeneousEquality as ≅
  using (_≅_; module ≅-Reasoning)
open import Relation.Binary.Morphism using (PosetHomomorphism)
import Relation.Binary.Morphism.Construct.Composition as RelMorComp
import Relation.Binary.Morphism.Construct.Identity as RelMorId
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import CategoryTheory.01-Categories.3-DefinitionOfACategory
open import CategoryTheory.Util

open Category

Sets : Category Set Morphism _≗_
Sets ._∘_ = Fun._∘′_
Sets .id A = Fun.id {A = A}
Sets ._—→-equiv_ A B = Setoid.isEquivalence (A ≡.→-setoid B)
Sets .∘-cong {x = g₁} {y = g₂} {u = f₁} {v = f₂} g₁≗g₂ f₁≗f₂ x = begin
  g₁ (f₁ x) ≡⟨ ≡.cong g₁ (f₁≗f₂ x) ⟩
  g₁ (f₂ x) ≡⟨ g₁≗g₂ (f₂ x) ⟩
  g₂ (f₂ x) ∎
  where
  open ≡-Reasoning
Sets .assoc f g h x = ≡.refl
Sets .unitˡ f x = ≡.refl
Sets .unitʳ f x = ≡.refl

Sets_fin : Category (Σ[ A ∈ Set ] ∃[ n ] A ↔ Fin n)
  (λ (A , _) (B , _) → A → B) _≗_
Sets_fin ._∘_ = _∘_ Sets
Sets_fin .id (A , _) = id Sets A
Sets_fin ._—→-equiv_ (A , _) (B , _) = _—→-equiv_ Sets A B
Sets_fin .∘-cong = ∘-cong Sets
Sets_fin .assoc = assoc Sets
Sets_fin .unitˡ = unitˡ Sets
Sets_fin .unitʳ = unitʳ Sets

module Pos where

  _≈ₐ_ : {P Q : Poset 0ℓ 0ℓ 0ℓ} → Rel.Rel (PosetHomomorphism P Q) 0ℓ
  _≈ₐ_ {P} {Q} F G = ∀ x → F.⟦ x ⟧ Q.≈ G.⟦ x ⟧
    where
    module Q = Poset Q
    module F = PosetHomomorphism F
    module G = PosetHomomorphism G

  Pos : Category (Poset 0ℓ 0ℓ 0ℓ) PosetHomomorphism _≈ₐ_
  Pos ._∘_ g f = RelMorComp.posetHomomorphism f g
  Pos .id = RelMorId.posetHomomorphism
  Pos ._—→-equiv_ P Q = record
    { refl = λ {F} x → Q.refl
    ; sym = λ F≈ₐG x → Q.sym (F≈ₐG x)
    ; trans = λ F≈ₐG G≈ₐH x → Q.trans (F≈ₐG x) (G≈ₐH x) }
    where
    module Q = Poset.Eq Q
  Pos .∘-cong {A} {B} {C} {G₁} {G₂} {F₁} {F₂} G₁≈ₐG₂ F₁≈ₐF₂ x = begin
    G₁.⟦ F₁.⟦ x ⟧ ⟧ ≈⟨ G₁.cong (F₁≈ₐF₂ x) ⟩
    G₁.⟦ F₂.⟦ x ⟧ ⟧ ≈⟨ G₁≈ₐG₂ F₂.⟦ x ⟧ ⟩
    G₂.⟦ F₂.⟦ x ⟧ ⟧ ∎
    where
    open ≈-Reasoning (Poset.Eq.setoid C)
    module G₁ = PosetHomomorphism G₁
    module G₂ = PosetHomomorphism G₂
    module F₁ = PosetHomomorphism F₁
    module F₂ = PosetHomomorphism F₂
  Pos .assoc {A} F G H x = H.cong (G.cong (F.cong A.Eq.refl))
    where
    module A = Poset A
    module F = PosetHomomorphism F
    module G = PosetHomomorphism G
    module H = PosetHomomorphism H
  Pos .unitˡ {A} F x = PosetHomomorphism.cong F (Poset.Eq.refl A)
  Pos .unitʳ {A} F x = PosetHomomorphism.cong F (Poset.Eq.refl A)

open Pos public using (Pos)

Rel : Category Set (λ A B → REL A B 0ℓ) _⇔_
Rel ._∘_ g f = f ; g
Rel .id A = _≡_
Rel ._—→-equiv_ A B = record
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
  (λ {a} {b} (b′ , aRb′ , b′≡b) → ≡.subst (R a) b′≡b aRb′) ,
  (λ {a} {b} aRb → b , aRb , ≡.refl)
Rel .unitʳ R =
  (λ {a} {b} (a′ , a≡a′ , a′Rb) → ≡.subst (flip R b) (≡.sym a≡a′) a′Rb) ,
  (λ {a} {b} aRb → a , ≡.refl , aRb)

𝟙 : Category ⊤ (λ _ _ → ⊤) _≡_
𝟙 ._∘_ _ _ = tt
𝟙 .id tt = tt
𝟙 ._—→-equiv_ _ _ = ≡.isEquivalence
𝟙 .∘-cong _ _ = ≡.refl
𝟙 .assoc _ _ _ = ≡.refl
𝟙 .unitˡ _ = ≡.refl
𝟙 .unitʳ _ = ≡.refl

module 𝟚 where

  data Obj : Set where
    ∗ ★ : Obj

  Arr : Obj → Obj → Set
  Arr ∗ _ = ⊤
  Arr ★ ∗ = ⊥
  Arr ★ ★ = ⊤

  𝟚 : Category Obj Arr _≡_
  𝟚 ._∘_ {∗} {_} {_} _ _ = tt
  𝟚 ._∘_ {★} {∗} {∗} _ ff = ff
  𝟚 ._∘_ {★} {★} {∗} ff _ = ff
  𝟚 ._∘_ {★} {∗} {★} _ _ = tt
  𝟚 ._∘_ {★} {★} {★} _ _ = tt
  𝟚 .id ∗ = tt
  𝟚 .id ★ = tt
  𝟚 ._—→-equiv_ _ _ = ≡.isEquivalence
  𝟚 .∘-cong {∗} {_} {_} _ _ = ≡.refl
  𝟚 .∘-cong {★} {_} {∗} _ _ = ≡.refl
  𝟚 .∘-cong {★} {_} {★} _ _ = ≡.refl
  𝟚 .assoc {∗} {_} {_} {_} _ _ _ = ≡.refl
  𝟚 .assoc {★} {_} {_} {∗} _ _ _ = ≡.refl
  𝟚 .assoc {★} {_} {_} {★} _ _ _ = ≡.refl
  𝟚 .unitˡ {∗} {_} _ = ≡.refl
  𝟚 .unitˡ {★} {∗} _ = ≡.refl
  𝟚 .unitˡ {★} {★} _ = ≡.refl
  𝟚 .unitʳ {∗} {_} _ = ≡.refl
  𝟚 .unitʳ {★} {∗} _ = ≡.refl
  𝟚 .unitʳ {★} {★} _ = ≡.refl

open 𝟚 public using (𝟚)

module 𝟛 where

  data Obj : Set where
    ∗ ★ ● : Obj

  Arr : Obj → Obj → Set
  Arr ∗ _ = ⊤
  Arr ★ ★ = ⊤
  Arr ★ ● = ⊤
  Arr ★ ∗ = ⊥
  Arr ● ● = ⊤
  Arr ● ∗ = ⊥
  Arr ● ★ = ⊥

  𝟛 : Category Obj Arr _≡_
  𝟛 ._∘_ {∗} {_} {_} _ _ = tt
  𝟛 ._∘_ {★} {_} {★} _ _ = tt
  𝟛 ._∘_ {★} {_} {●} _ _ = tt
  𝟛 ._∘_ {★} {∗} {∗} _ ff = ff
  𝟛 ._∘_ {★} {★} {∗} ff _ = ff
  𝟛 ._∘_ {★} {●} {∗} ff _ = ff
  𝟛 ._∘_ {●} {_} {●} _ _ = tt
  𝟛 ._∘_ {●} {∗} {∗} _ ff = ff
  𝟛 ._∘_ {●} {★} {∗} ff _ = ff
  𝟛 ._∘_ {●} {●} {∗} ff _ = ff
  𝟛 ._∘_ {●} {∗} {★} _ ff = ff
  𝟛 ._∘_ {●} {★} {★} _ ff = ff
  𝟛 ._∘_ {●} {●} {★} ff _ = ff
  𝟛 .id ∗ = tt
  𝟛 .id ★ = tt
  𝟛 .id ● = tt
  𝟛 ._—→-equiv_ _ _ = ≡.isEquivalence
  𝟛 .∘-cong {∗} {_} {_} _ _ = ≡.refl
  𝟛 .∘-cong {★} {_} {∗} _ _ = ≡.refl
  𝟛 .∘-cong {★} {_} {★} _ _ = ≡.refl
  𝟛 .∘-cong {★} {_} {●} _ _ = ≡.refl
  𝟛 .∘-cong {●} {_} {∗} _ _ = ≡.refl
  𝟛 .∘-cong {●} {_} {★} _ _ = ≡.refl
  𝟛 .∘-cong {●} {_} {●} _ _ = ≡.refl
  𝟛 .assoc {∗} {_} {_} {_} _ _ _ = ≡.refl
  𝟛 .assoc {★} {_} {_} {∗} _ _ _ = ≡.refl
  𝟛 .assoc {★} {_} {_} {★} _ _ _ = ≡.refl
  𝟛 .assoc {★} {_} {_} {●} _ _ _ = ≡.refl
  𝟛 .assoc {●} {_} {_} {∗} _ _ _ = ≡.refl
  𝟛 .assoc {●} {_} {_} {★} _ _ _ = ≡.refl
  𝟛 .assoc {●} {_} {_} {●} _ _ _ = ≡.refl
  𝟛 .unitˡ {∗} {_} _ = ≡.refl
  𝟛 .unitˡ {★} {∗} _ = ≡.refl
  𝟛 .unitˡ {★} {★} _ = ≡.refl
  𝟛 .unitˡ {★} {●} _ = ≡.refl
  𝟛 .unitˡ {●} {∗} _ = ≡.refl
  𝟛 .unitˡ {●} {★} _ = ≡.refl
  𝟛 .unitˡ {●} {●} _ = ≡.refl
  𝟛 .unitʳ {∗} {_} _ = ≡.refl
  𝟛 .unitʳ {★} {∗} _ = ≡.refl
  𝟛 .unitʳ {★} {★} _ = ≡.refl
  𝟛 .unitʳ {★} {●} _ = ≡.refl
  𝟛 .unitʳ {●} {∗} _ = ≡.refl
  𝟛 .unitʳ {●} {★} _ = ≡.refl
  𝟛 .unitʳ {●} {●} _ = ≡.refl

open 𝟛 public using (𝟛)

𝟘 : Category ⊥ (λ _ _ → ⊤) _≡_
𝟘 ._∘_ _ _ = tt
𝟘 .id _ = tt
𝟘 ._—→-equiv_ _ _ = ≡.isEquivalence
𝟘 .∘-cong _ _ = ≡.refl
𝟘 .assoc _ _ _ = ≡.refl
𝟘 .unitˡ _ = ≡.refl
𝟘 .unitʳ _ = ≡.refl

record Functor {ℓoC ℓaC ℓ≈ₐC ℓoD ℓaD ℓ≈ₐD}
  {ObjC : Set ℓoC} {_—→C_ : ObjC → ObjC → Set ℓaC}
  {_≈ₐC_ : {A B : ObjC} → Rel.Rel (A —→C B) ℓ≈ₐC}
  {ObjD : Set ℓoD} {_—→D_ : ObjD → ObjD → Set ℓaD}
  {_≈ₐD_ : {A B : ObjD} → Rel.Rel (A —→D B) ℓ≈ₐD}
  (C : Category ObjC _—→C_ _≈ₐC_) (D : Category ObjD _—→D_ _≈ₐD_)
  : Set (ℓoC ⊔ ℓaC ⊔ ℓ≈ₐC ⊔ ℓoD ⊔ ℓaD ⊔ ℓ≈ₐD) where
  private
    module C = Category C
    module D = Category D
  field
    Fₒ : ObjC → ObjD
    Fₐ : {A B : ObjC} → (A —→C B) → (Fₒ A —→D Fₒ B)
    Fₐ-cong : {A B : ObjC} → _≈ₐC_ {A} {B} =[ Fₐ ]⇒ _≈ₐD_
    F₁ : {A : ObjC} → Fₐ (C.id A) ≈ₐD D.id (Fₒ A)
    F∘ : {A A′ A′′ : ObjC} → (f : A —→C A′) → (g : A′ —→C A′′) →
      Fₐ (g C.∘ f) ≈ₐD (Fₐ g D.∘ Fₐ f)

module Cat where

  CatObj : Set₁
  CatObj = Σ[ Obj ∈ Set ] Σ[ Arr ∈ (Obj → Obj → Set) ]
    Σ[ ≈ₐ ∈ ({A B : Obj} → Rel.Rel (Arr A B) 0ℓ) ] Category Obj Arr ≈ₐ

  _Cat—→_ : CatObj → CatObj → Set
  _Cat—→_ (_ , _ , _ , C) (_ , _ , _ , D) = Functor C D

  module _
    {(ObjC , _—→C_ , _≈ₐC_ , C) (_ , _—→D_ , _≈ₐD_ , D) : CatObj}
    (F G : Functor C D) where

    private
      module F = Functor F
      module G = Functor G

    module _ (Fₒ≗Gₒ : F.Fₒ ≗ G.Fₒ) {A B : ObjC} where

      rewrite-dom-cod : (F.Fₒ A —→D F.Fₒ B) → (G.Fₒ A —→D G.Fₒ B)
      rewrite-dom-cod f rewrite Fₒ≗Gₒ A | Fₒ≗Gₒ B = f

      rewrite-dom-cod-≅ : (f : F.Fₒ A —→D F.Fₒ B) → f ≅ rewrite-dom-cod f
      rewrite-dom-cod-≅ f rewrite Fₒ≗Gₒ A | Fₒ≗Gₒ B = ≅.refl

      rewrite-dom-cod-cong :
        _≈ₐD_ {F.Fₒ A} {F.Fₒ B} =[ rewrite-dom-cod ]⇒ _≈ₐD_ {G.Fₒ A} {G.Fₒ B}
      rewrite-dom-cod-cong {f} {g} = subst₂-type-and-value _—→D_ _≈ₐD_
        (Fₒ≗Gₒ A) (Fₒ≗Gₒ B) (rewrite-dom-cod-≅ f) (rewrite-dom-cod-≅ g)

    _Cat≈ₐ_ : Set
    _Cat≈ₐ_ = Σ[ Fₒ≗Gₒ ∈ F.Fₒ ≗ G.Fₒ ]
      ({A B : ObjC} → (f : A —→C B) → rewrite-dom-cod Fₒ≗Gₒ (F.Fₐ f) ≈ₐD G.Fₐ f)

  Cat : Category CatObj _Cat—→_ _Cat≈ₐ_
  Cat ._∘_ {_ , _ , _ , C} {_ , _ , _ , D} {_ , _ , _ , E} G F = record
    { Fₒ = G.Fₒ Fun.∘ F.Fₒ
    ; Fₐ = G.Fₐ Fun.∘ F.Fₐ
    ; Fₐ-cong = G.Fₐ-cong Fun.∘ F.Fₐ-cong
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
        G.Fₐ (F.Fₐ g) E.∘ G.Fₐ (F.Fₐ f) ∎ }
    where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G
  Cat .id (_ , _ , _ , C) = record
    { Fₒ = Fun.id
    ; Fₐ = Fun.id
    ; Fₐ-cong = Fun.id
    ; F₁ = λ {A} → IsEquivalence.refl (A C.—→-equiv A)
    ; F∘ = λ {A} {A′} {A′′} f g → IsEquivalence.refl (A C.—→-equiv A′′) }
    where
    module C = Category C
  Cat ._—→-equiv_ _ (_ , _—→D_ , _≈ₐD_ , D) = record
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
            (subst₂-type-and-value _—→D_ _≈ₐD_ (Gₒ≗Fₒ A) (Gₒ≗Fₒ B)
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
            (subst₂-type-and-value _—→D_ _≈ₐD_ (Gₒ≗Hₒ A) (Gₒ≗Hₒ B)
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
  Cat .∘-cong {_} {_ , _—→D_ , _ , _} {_ , _—→E_ , _≈ₐE_ , E} {G₁} {G₂}
    {F₁} {F₂} (G₁ₒ≗G₂ₒ , G₁ₐ≈ₐG₂ₐ) (F₁ₒ≗F₂ₒ , F₁ₐ≈ₐF₂ₐ) = G₁ₒF₁ₒ≗G₂ₒF₂ₒ ,
      λ {A} {B} f → ≅.subst (_≈ₐE G₂F₂.Fₐ f)
        (let open ≅-Reasoning
         in begin
              rewrite-dom-cod G₁ G₂ G₁ₒ≗G₂ₒ
                (G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f)))
            ≅˘⟨ rewrite-dom-cod-≅ G₁ G₂ G₁ₒ≗G₂ₒ
                  (G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f))) ⟩
              G₁.Fₐ (rewrite-dom-cod F₁ F₂ F₁ₒ≗F₂ₒ (F₁.Fₐ f))
            ≅˘⟨ cong-type-and-value _—→D_ _—→E_ G₁.Fₒ G₁.Fₐ (F₁ₒ≗F₂ₒ A)
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
    module E = Category E
    module G₁ = Functor G₁
    module G₂ = Functor G₂
    module F₁ = Functor F₁
    module F₂ = Functor F₂
    G₁F₁ = _∘_ Cat G₁ F₁
    G₂F₂ = _∘_ Cat G₂ F₂
    module G₂F₂ = Functor G₂F₂
    G₁ₒF₁ₒ≗G₂ₒF₂ₒ : G₁.Fₒ Fun.∘ F₁.Fₒ ≗ G₂.Fₒ Fun.∘ F₂.Fₒ
    G₁ₒF₁ₒ≗G₂ₒF₂ₒ A = begin
      G₁.Fₒ (F₁.Fₒ A) ≡⟨ ≡.cong G₁.Fₒ (F₁ₒ≗F₂ₒ A) ⟩
      G₁.Fₒ (F₂.Fₒ A) ≡⟨ G₁ₒ≗G₂ₒ (F₂.Fₒ A) ⟩
      G₂.Fₒ (F₂.Fₒ A) ∎
      where
      open ≡-Reasoning
  Cat .assoc {_} {_} {_} {_ , _ , _ , C₄} F G H = (λ A → ≡.refl) ,
    λ {A} {B} f →
      IsEquivalence.refl (H.Fₒ (G.Fₒ (F.Fₒ A)) C₄.—→-equiv H.Fₒ (G.Fₒ (F.Fₒ B)))
    where
    module C₄ = Category C₄
    module F = Functor F
    module G = Functor G
    module H = Functor H
  Cat .unitˡ {_} {_ , _ , _ , D} F = (λ A → ≡.refl) ,
    λ {A} {B} f → IsEquivalence.refl (F.Fₒ A D.—→-equiv F.Fₒ B)
    where
    module D = Category D
    module F = Functor F
  Cat .unitʳ {_} {_ , _ , _ , D} F = (λ A → ≡.refl) ,
    λ {A} {B} f → IsEquivalence.refl (F.Fₒ A D.—→-equiv F.Fₒ B)
    where
    module D = Category D
    module F = Functor F

open Cat public using (Cat)
