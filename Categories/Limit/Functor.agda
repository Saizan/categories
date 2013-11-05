open import Level
open import Categories.Category
open import Categories.Colimit
module Categories.Limit.Functor {o ℓ e : Level} {o′ ℓ′ e′} {C : Category o′ ℓ′ e′} (cocomplete : Cocomplete o ℓ e (Category.op C)) where


import Categories.Functor as Cat
open Cat using (Functor; module Functor)
open import Categories.FunctorCategory
open import Categories.NaturalTransformation
open import Categories.Functor.Constant
open import Categories.Categories
open import Categories.Grothendieck
open import Categories.Opposite
import Categories.Colimit.Functor
open Categories.Colimit.Functor cocomplete

lim : ∀ {o₀ ℓ₀ e₀} {O : Category o₀ ℓ₀ e₀} (P : Functor (Category.op O) (Categories o ℓ e)) 
        → (Functor (Category.op (Gr P)) C) → (Functor O C)
lim P F = Functor.op (colim P (Functor.op F))
{-
limF : ∀ {o₀ ℓ₀ e₀} {O : Category o₀ ℓ₀ e₀} (P : Functor (Category.op O) (Categories o ℓ e)) 
        → Functor (Functors (Category.op (Gr P)) C) (Functors O C)
limF P = opF Cat.∘ Functor.op (colimF P) Cat.∘ Functor.op opF
-}

