{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.Any where

open import Level
open import Relation.Nullary as Dec
open import Relation.Unary using (Pred; _⊆_; Decidable; Satisfiable)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; node)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional
import Data.List.Relation.Unary.Any as List
open import Data.Product using (∃; _,_)

private
  variable
    ℓ ℓ₁ : Level
    A : Set ℓ
    P Q : Pred A ℓ₁
    t : Rose A
    
data Any {A : Set ℓ} (P : Pred A ℓ₁) : Pred (Rose A) (ℓ ⊔ ℓ₁) where
  here  : ∀ {r cs}   → P r              → Any P (node r cs)
  there : ∀ {t cs r} → Any P t → t ∈ cs → Any P (node r cs)

map : P ⊆ Q → Any P t → Any Q t
map g (here x) = here (g x)
map g (there t x) = there (map g t) x

lookup : {P : Pred A ℓ₁} → Any P t → A
lookup (here {r} _) = r
lookup (there ts _) = lookup ts

satisfied : Any P t → ∃ P
satisfied (here x)   = _ , x
satisfied (there t x) = satisfied t

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → Decidable (Any P)
any?' : Decidable P → Decidable (List.Any (Any P))
any?' P? [] = no (λ ())
any?' P? (t ∷ ts) with any? P? t
... | yes p = yes (List.here p)
... | no ¬p with any?' P? ts 
... | yes ps = yes (List.there ps)
... | no ¬ps = no (λ { (List.here px) → ¬p px
                     ; (List.there x) → ¬ps x })
any? P? (node root children) with P? root 
... | yes p = yes (here p)
... | no ¬p with any?' P? children
any? P? (node root children) | no ¬p | yes ps with find ps
... | fst , fst₁ , snd = yes (there snd fst₁)
any? P? (node root children) | no ¬p | no ps' = no (λ { (here x) → ¬p x
                                                      ; (there x x₁) → ps' (lose x₁ x) })

satisfiable : Satisfiable P → Satisfiable (Any P)
satisfiable (x , Px) = (node x []) , (here Px) 
