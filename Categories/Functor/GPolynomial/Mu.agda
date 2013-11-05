{-# OPTIONS --no-termination-check #-}
--{-# OPTIONS --no-positivity-check #-}
--{-# OPTIONS -v 5 -v tc.decl:20 -v tc.pos:500 #-}
{-# OPTIONS -v tc.conv.irr:20 #-}
module Categories.Functor.GPolynomial.Mu where
open import Categories.Support.Equivalence using (Setoid; module Setoid)

open import Categories.Category
open import Categories.Functor as Cat
open import Categories.Agda
open import Data.Product
open import Level
open import Categories.Grothendieck
open import Categories.FunctorCategory
open import Categories.Support.PropositionalEquality
open import Categories.Support.IProduct
open import Categories.NaturalTransformation
open import Categories.Categories
open import Categories.Product
open import Categories.Colimit
open import Categories.Colimit.Functor
open import Categories.Limit.Functor

open import Categories.Functor.GPolynomial
open import Categories.Support.Experimental

import Categories.Support.ZigZag as ZigZag
open import Categories.Support.Equivalence

module MuTypes {l : CLevel} (I : Category` l) (o₁ o₂ : _) (F : ICCat {l} {l} I I o₁ o₂) where
  open ICCat F

  ⟦F⟧ : Functor I (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂)) -> I.Obj -> Set _
  ⟦F⟧ X i = Setoid.Carrier (Functor.F₀ (sem X) i)
  ⟦F⟧R : (X
            : Functor I (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂)))
           (i : I.Obj) →
           Setoid.Carrier (Functor.F₀ (sem X) i) →
           Setoid.Carrier (Functor.F₀ (sem X) i) → Set (c-lvl o₁ ⊔ c-lvl o₂)
  ⟦F⟧R = \ X i -> Setoid._≈_ (Functor.F₀ (sem X) i)
  
  postulate 
    TODO TODOfmap : ∀ {l} {A : Set l} -> A
    TODOcong : ∀ {l} {A : Set l} -> A

  mutual
    Body : I.Obj -> Set _
    Body i = Σ (Category.Obj (S.F₀ i)) (λ x₁ →
        Σ′ ((j : Category.Obj (P.F₀ (i , x₁))) → Mu (r.F₀ ((i , x₁) , j)))
        (λ f →
        {a b : Category.Obj (P.F₀ (i , x₁))}
        (h : (P.F₀ (i , x₁) Category.⇒ a) b) →
        MuRel (r.F₀ ((i , x₁) , a))
        (fmap
        (r.F₁
          ((I.id ,
            ≣-subst₂ (Category._⇒_ (S.F₀ i))
            (≣-relevant TODO) ≣-refl
            (Category.id (S.F₀ i)))
          ,
          ≣-subst₂ (Category._⇒_ (P.F₀ (i , x₁)))
          (≣-relevant TODO) ≣-refl h))
        (f b))
        (f a)))

    data Mu (i : I.Obj) : Set _ where
      con : Body i -> Mu i
  
--    data MuRel (i : I.Obj) : Mu i -> Mu i -> Set _ where
--      conRel : ∀ {m n : Body i} -> x i m n -> MuRel i (con m) (con n)

  
    MuF : Functor I (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂))
    MuF = record 
      { F₀ = λ i → record { Carrier = Mu i
                          ; _≈_ = MuRel i; isEquivalence = {!!} }
      ; F₁ = λ f → record { _⟨$⟩_ = fmap f; cong = TODOfmap }
      ; identity = {!!}
      ; homomorphism = {!!}
      ; F-resp-≡ = {!!}
      }
    
    MuRel : (i : I.Obj) -> (m n : Mu i) -> Set _
    MuRel i (con m) (con n) = ⟦F⟧R MuF i m n
{-
    x : (i : I.Obj) -> (m n : Body i) -> Set _
    x i m n = ⟦F⟧R MuF i m n
    
    .refl′ : ∀ {i} -> {x : Mu i} → MuRel i x x
    refl′ {i} {con x} = TODO

    .sym′ : ∀ {i} -> {x y : Mu i} → MuRel i x y -> MuRel i y x
    sym′ {i} {con x} {con y} (conRel eq) = {!eq!}
-}  
    fmap : {A B : I.Obj} -> I [ A , B ] -> Mu A -> Mu B
    fmap {A} {B} f (con (s , (t , t-nat))) = con ((Functor.F₀ (S.F₁ f) s) , ((λ j → fmap (r.F₁ ((f , (C.id (S.F₀ B))) , (C.id (P.F₀ (A , s))))) 
           (t (Functor.F₀ (P.F₁ (f , (C.id (S.F₀ B)))) j))) , {!!}))


{-
  ZigZag.Alternating′
  (λ Xx Yy →
     Σ (Data.Product.proj₁ Xx J.⇒ Data.Product.proj₁ Yy)
     (λ f →
        Categories.Support.Equivalence.I→R-Wrapper
        (_≈_ (F₀ (Data.Product.proj₁ Yy))) (F₁ f ⟨$⟩ Data.Product.proj₂ Xx)
        (Data.Product.proj₂ Yy)))
-}
{-
    .refl′ : ∀ {i} -> {x : Mu i} → MuRel i x x
    refl′ {i} {con x} = ?
-}
