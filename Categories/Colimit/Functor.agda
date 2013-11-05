open import Level
open import Categories.Category
open import Categories.Colimit
module Categories.Colimit.Functor {o ℓ e : Level} {o′ ℓ′ e′} {C : Category o′ ℓ′ e′} (cocomplete : Cocomplete o ℓ e C) where


import Categories.Functor as Cat
open Cat using (Functor; module Functor)
open import Categories.NaturalTransformation
open import Categories.FunctorCategory
open import Categories.Functor.Constant
open import Categories.Categories
open import Categories.Grothendieck
open import Categories.Opposite

open Cocomplete cocomplete
private module C = Category C
open import Categories.Lan

colim : ∀ {o₀ ℓ₀ e₀} {O : Category o₀ ℓ₀ e₀} (S : Functor O (Categories o ℓ e)) 
        → Functor (Gr S) C → Functor O C
colim {O = O} S F = record 
  { F₀ = λ o → Colimit.∃F (colimit {S.F₀ o} (F Cat.∘ inGr S o))
  ; F₁ = λ {A} {B} f → G.< (G.ι {B} ∘ʳ S.F₁ f) ∘₁ (F ∘ˡ inGr-nat S f) >
  ; identity = TODO
  ; homomorphism = TODO
  ; F-resp-≡ = TODO
  }
  module colim where
    module O = Category O
    module S = Functor S
    module F = Functor F
    module G {o} = Colimit (colimit {S.F₀ o} (F Cat.∘ inGr S o))
    postulate TODO : ∀ {l} {A : Set l} -> A

colimF : ∀ {o₀ ℓ₀ e₀} {O : Category o₀ ℓ₀ e₀} (S : Functor O (Categories o ℓ e)) 
        → Functor (Functors (Gr S) C) (Functors O C)
colimF {O = O} S = record {
                     F₀ = colim S;
                     F₁ = λ {A} {B} η → record { η = λ X → colim.G.<_> S A ((colim.G.ι S B) ∘₁ (η ∘ʳ inGr S X)); 
                                                 commute = TODO };
                     identity = TODO;
                     homomorphism = TODO;
                     F-resp-≡ = TODO }
  where
    module O = Category O
    module S = Functor S
    open Colimit renaming (<_> to [_]<_>)
    postulate TODO : ∀ {l} {A : Set l} -> A

open import Data.Product

isLan : ∀ {o₀ ℓ₀ e₀} {O : Category o₀ ℓ₀ e₀} (S : Functor O (Categories o ℓ e)) 
        → (F : Functor (Gr S) C) → Lan (DomGr S) F
isLan {O = O} S F = record 
  { L = colim S F
  ; ε = record { η = λ {(o , So) → NaturalTransformation.η (G.ι {o}) So}
               ; commute = λ { {x , Sx} {y , Sy} (f , φ) → TODO} }
  ; σ = λ M → λ α → record 
    { η = λ X → G.<_> {X} {Functor.F₀ M X} (record { η = λ X₁ → NaturalTransformation.η α (X , X₁); commute = TODO })
    ; commute = TODO }
  ; σ-unique = TODO
  ; commutes = TODO }
    module isLan where
    module O = Category O
    module S = Functor S
    module F = Functor F
    module G {o} = Colimit (colimit {S.F₀ o} (F Cat.∘ inGr S o))
    postulate TODO : ∀ {l} {A : Set l} -> A
