module Categories.Functor.GPolynomial where
open import Categories.Category
open import Categories.Functor as Cat
open import Categories.Agda
open import Data.Product
open import Categories.Lan
open import Categories.Ran
open import Level

import Categories.End

record CLevel : Set where
  constructor CL_,_,_
  field
    o-lvl : Level
    ℓ-lvl : Level
    e-lvl : Level

open CLevel

Category` : (l : CLevel) -> Set (suc (o-lvl l ⊔ (ℓ-lvl l ⊔ e-lvl l))) 
Category` (CL o , ℓ , e) = Category o ℓ e

c-lvl : CLevel -> Level
c-lvl (CL o , ℓ , e) = o ⊔ ℓ ⊔ e



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


open import Categories.Comma
open import Categories.Agda.ISetoids.Complete
open import Categories.Agda.ISetoids.Cocomplete
    
Categories` : (cl : CLevel) -> Category _ _ _
Categories` (CL o , l , e) = Categories o l e

record ICCat {l₀ l₁ : CLevel} (I : Category` l₀) (O : Category` l₁) (o₁ o₂ : _)
       : Set (c-lvl l₀ ⊔ c-lvl l₁ ⊔ suc (c-lvl o₁) ⊔ suc (c-lvl o₂)) where
  constructor ic
  field
    S : Functor O (Categories` o₁)
    P : Functor (Category.op (Gr S)) (Categories` o₂)
    r : Functor (Category.op (Gr P)) I

  module S = Functor S
  module P = Functor P
  module r = Functor r
  module I = Category I
  module O = Category O
  module C = Category
  module F = Functor

  
  sem : (Functor I (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂))) -> (Functor O (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂))) 
  sem X = colim (ISetoidsCocomplete {o-lvl o₁} {ℓ-lvl o₁} {e-lvl o₁} {c-lvl o₂} {zero}) S 
           (lim (ISetoidsComplete {o-lvl o₂} {ℓ-lvl o₂} {e-lvl o₂} {c-lvl o₁} {zero}) P 
             (X ∘ r))
{-
  ⟦_⟧ : Functor (Functors I (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂))) 
                (Functors O (ISetoids (c-lvl o₁ ⊔ c-lvl o₂) (c-lvl o₁ ⊔ c-lvl o₂)))
  ⟦_⟧ = colimF (ISetoidsCocomplete {o-lvl o₁} {ℓ-lvl o₁} {e-lvl o₁} {c-lvl o₂} {zero}) S 
          ∘ limF (ISetoidsComplete {o-lvl o₂} {ℓ-lvl o₂} {e-lvl o₂} {c-lvl o₁} {zero}) P 
              ∘ Cat[-∘ r ]
    where
      module GrS where
        open Category (Grothendieck S) public
        open Groth S public
      module GrP where
        open Category (Grothendieck P) public
        open Groth P public
-}
postulate
  lan : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} (F : Functor A B) (P : Functor A (Sets o)) -> Lan F P
  ran : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} (F : Functor A B) (P : Functor A (Sets o)) -> Ran F P

lanF : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} (F : Functor A B) (P : Functor A (Sets o)) -> Functor B (Sets o)
lanF F P = Lan.L (lan F P)

ranF : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} (F : Functor A B) (P : Functor A (Sets o)) -> Functor B (Sets o)
ranF F P = Ran.R (ran F P)

record GPF  {l₀ l₁ : CLevel} (I : Category` l₀) (O : Category` l₁) (l₂ l₃ : CLevel) 
             : Set (c-lvl l₀ ⊔ c-lvl l₁ ⊔ suc (c-lvl l₂) ⊔ suc (c-lvl l₃)) where
  field
    {S} : Category` l₂
    {P} : Category` l₃ 
    q : Functor S O
    f : Functor P S
    r : Functor P I
  module S = Category S
  module P = Category P
  module q = Functor q
  module f = Functor f
  module r = Functor r

  ⟦_⟧ : ∀ {o} -> Functor I (Sets o) -> Functor O (Sets o)
  ⟦_⟧ X = lanF q (ranF f (X ∘ r))
          
open import Categories.Support.Experimental
open import Categories.Comma
open import Categories.Functor.Constant
open import Categories.Functor.Diagonal
open import Categories.Terminal using () renaming (OneC to One)


GPFtoIC : {l₀ l₁ l₂ l₃ : CLevel} (I : Category` l₀) (O : Category` l₁) → GPF {l₀} {l₁} I O l₂ l₃ 
              → ICCat {l₀} {l₁} I O _ _
GPFtoIC I O gp = ic S P r
  where
    module gp = GPF gp
    module O = Category O
    module I = Category I
    postulate
      TODO : forall {l} {A : Set l} -> A
 
    S : Functor O (Categories _ _ _)
    S = CommaF gp.q (ΔF (One {zero} {zero} {zero}))

    S⇒S : Functor (Gr S) gp.S
    S⇒S = record 
      { F₀ = (λ x → Comma.Obj.α (proj₂ x))
      ; F₁ = λ x → Comma.Hom.g (proj₂ x)
      ; identity = TODO
      ; homomorphism = TODO
      ; F-resp-≡ = TODO
      }

    
    module S⇒S = Functor S⇒S

    P : Functor (Category.op (Gr S)) (Categories _ _ _)
    P = CommaF gp.f.op (ΔF (One {zero} {zero} {zero})) ∘ S⇒S.op

    P⇒P : Functor (Category.op (Gr P)) gp.P
    P⇒P = record 
      { F₀ = (λ x → Comma.Obj.α (proj₂ x))
      ; F₁ = λ x → Comma.Hom.g (proj₂ x)
      ; identity = TODO
      ; homomorphism = TODO
      ; F-resp-≡ = TODO
      } 

    r : Functor (Category.op (Gr P)) I
    r = gp.r ∘ P⇒P

ICtoGPF : {l₀ l₁ : CLevel}{o₁ o₂ : _} (I : Category` l₀) (O : Category` l₁) → ICCat {l₀} {l₁} I O o₁ o₂ → 
          GPF {l₀} {l₁} I O (CL _ , _ , _) (CL _ , _ , _)
ICtoGPF I O c = record { 
  S = Gr ic.S; 
  P = Category.op (Gr ic.P); 
  q = DomGr ic.S; 
  f = Functor.op (DomGr ic.P); 
  r = ic.r } where
  module ic = ICCat c
  module GrS = Category (Gr ic.S)

