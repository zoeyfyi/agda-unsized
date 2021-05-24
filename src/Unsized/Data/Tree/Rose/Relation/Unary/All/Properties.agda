{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.All.Properties where

open import Level
open import Data.Empty using (⊥-elim)
open import Relation.Nullary as Dec
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary as B using (REL; Setoid; _Respects_)
open import Relation.Unary using (Pred; Decidable; Satisfiable; _∩_; IUniversal; _⇒_) renaming (_⊆_ to _⋐_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose as Rose
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₗ_; find to findₗ)
import Unsized.Data.Tree.Rose.Membership.Setoid as SetoidMembership
open import Unsized.Data.Tree.Rose.Membership.Propositional
import Data.List.Relation.Unary.All as List
import Data.List.Relation.Unary.Any as AnyList
open import Data.Product as Prod using (∃; _,_)
open import Unsized.Data.Tree.Rose.Relation.Unary.Any as Any using (Any)
open import Relation.Binary.PropositionalEquality as P using (refl; _≡_; cong₂; _≗_)
open P.≡-Reasoning
open import Unsized.Data.Tree.Rose.Relation.Unary.Any using (here; there)
open import Unsized.Data.Tree.Rose.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllList
import Data.Maybe.Relation.Unary.All as Maybe
open import Function.Base
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse using (_↔_; inverse)
open import Function.Surjection using (_↠_; surjection)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set ℓ
    P : Pred A ℓ₁
    Q : Pred A ℓ₂
    R : Pred A ℓ₃
    t : Rose A
    cs : Forest A

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

All⇒Any : ∀ {t} → All P t → Any P t
All⇒Any (node p _) = here p

¬Any⇒All¬ : ∀ (t : Rose A) → ¬ Any P t → All (¬_ ∘ P) t
¬Any⇒All¬ᶠ : ∀ (cs : Forest A) → (∀ {t} → t ∈ₗ cs → ¬ Any P t) → Allᶠ (¬_ ∘ P) cs
¬Any⇒All¬ (node root children) ¬p = node (λ z → ¬p (here z)) (¬Any⇒All¬ᶠ children λ x → ¬p ∘ there x)
¬Any⇒All¬ᶠ [] ¬p = List.[]
¬Any⇒All¬ᶠ (c ∷ cs) ¬p = ¬Any⇒All¬ c (¬p (AnyList.here refl)) List.∷ ¬Any⇒All¬ᶠ cs (λ z → ¬p (AnyList.there z)) 

All¬⇒¬Any : ∀ (t : Rose A) → All (¬_ ∘ P) t → ¬ Any P t
All¬⇒¬Any (node root children) (node x x₁) (here x₂) = x x₂
All¬⇒¬Any (node root children) (node x x₁) (there x₂ y) = All¬⇒¬Any _ (List.lookup x₁ x₂) y

¬All⇒Any¬ : Decidable P → ∀ t → ¬ All P t → Any (¬_ ∘ P) t
¬All⇒Any¬ᶠ : Decidable P → ∀ cs → AnyList.Any (¬_ ∘ All P) cs → Prod.Σ[ c ∈ _ ] c ∈ₗ cs Prod.× Any (¬_ ∘ P) c
¬All⇒Any¬ dec (node root children) ¬∀ with dec root | List.all? (all? dec) children
... | yes pr | yes pcs = ⊥-elim (¬∀ (node pr pcs))
... | no ¬pr | _       = here ¬pr
... | yes _  | no ¬pcs with ¬All⇒Any¬ᶠ dec children (AllList.¬All⇒Any¬ (all? dec) children ¬pcs) 
... | t1 , t2 , t3 = there t2 t3
¬All⇒Any¬ᶠ dec (c ∷ cs) (AnyList.here px) = _ , AnyList.here refl , ¬All⇒Any¬ dec _ px
¬All⇒Any¬ᶠ dec (x ∷ cs) (AnyList.there xs) with ¬All⇒Any¬ᶠ dec cs xs 
... | t1 , t2 , t3 = t1 , AnyList.there t2 , t3

Any¬⇒¬All : Any (¬_ ∘ P) t → ¬ All P t
Any¬⇒¬All (here x) = x ∘ All.root
Any¬⇒¬All (there x x₂) x₁ = Any¬⇒¬All x₂ (List.lookup (All.children x₁) x)

¬Any↠All¬ : (¬ Any P t) ↠ All (¬_ ∘ P) t
¬Any↠All¬ = surjection (¬Any⇒All¬ _) (All¬⇒¬Any _) to∘from
  where 
    to∘fromᶠ : ∀ (¬cs : Allᶠ (¬_ ∘ P) cs) → ¬Any⇒All¬ᶠ cs (λ x x₁ → All¬⇒¬Any _ (List.lookup ¬cs x) x₁) ≡ ¬cs
    to∘from : ∀ (¬p : All (¬_ ∘ P) t) → ¬Any⇒All¬ t (All¬⇒¬Any t ¬p) ≡ ¬p
    to∘from (node x x₁) = cong₂ node refl (to∘fromᶠ x₁)
    to∘fromᶠ List.[] = refl
    to∘fromᶠ (px List.∷ ¬cs) = cong₂ List._∷_ (to∘from px) (to∘fromᶠ ¬cs)
    
Any¬⇔¬All : Decidable P → Any (¬_ ∘ P) t ⇔ (¬ All P t)
Any¬⇔¬All dec = equivalence Any¬⇒¬All (¬All⇒Any¬ dec _)

module _ {_~_ : REL A B ℓ} where
  All-swap : ∀ {t1 t2} → All (λ x → All (x ~_) t2) t1 → All (λ y → All (_~ y) t1) t2
  All-swap {node root₁ children₁} {node root₂ children₂} (node x x₁) = node (node (All.root x) (List.map (All.map All.root) x₁)) 
    (List.tabulate λ x₂ → tabulate (λ x₄ → node (lookup x (there x₂ x₄)) (List.map (All.map (λ x₇ → lookup x₇ (there x₂ x₄))) x₁)))

------------------------------------------------------------------------
-- Properties of operations over `All`
------------------------------------------------------------------------
-- map

map-id : ∀ (ts : All P t) → All.map id ts ≡ ts
mapᶠ-id : ∀ (css : Allᶠ P cs) → All.mapᶠ id css ≡ css
map-id (node r cs) = cong₂ node refl (mapᶠ-id cs)
mapᶠ-id List.[] = refl
mapᶠ-id (px List.∷ css) = cong₂ List._∷_ (map-id px) (mapᶠ-id css)


map-cong : ∀ {f : P ⋐ Q} {g : P ⋐ Q} (pt : All P t) →
           (∀ {x} → f {x} ≗ g) → All.map f pt ≡ All.map g pt
mapᶠ-cong : ∀ {f : P ⋐ Q} {g : P ⋐ Q} (pcs : Allᶠ P cs) →
            (∀ {x} → f {x} ≗ g) → All.mapᶠ f pcs ≡ All.mapᶠ g pcs
map-cong (node pr pcs) feq = cong₂ node (feq pr) (mapᶠ-cong pcs feq)
mapᶠ-cong List.[] feq = refl
mapᶠ-cong (px List.∷ pcs) feq = cong₂ List._∷_ (map-cong px feq) (mapᶠ-cong pcs feq)

map-compose : ∀ {f : P ⋐ Q} {g : Q ⋐ R} (pt : All P t) →
              All.map g (All.map f pt) ≡ All.map (g ∘ f) pt
mapᶠ-compose : ∀ {f : P ⋐ Q} {g : Q ⋐ R} (pcs : Allᶠ P cs) →
               All.mapᶠ g (All.mapᶠ f pcs) ≡ All.mapᶠ (g ∘ f) pcs
map-compose (node x cs) = cong₂ node refl (mapᶠ-compose cs)   
mapᶠ-compose List.[] = refl
mapᶠ-compose (px List.∷ pcs) = cong₂ List._∷_ (map-compose px) (mapᶠ-compose pcs)

lookup-map : ∀ {x : A} {f : P ⋐ Q} (pt : All P t) (i : x ∈ t) →
             lookup (All.map f pt) i ≡ f (lookup pt i)
lookup-mapᶠ : ∀ {f : P ⋐ Q} (pcs : Allᶠ P cs) (i : t ∈ₗ cs) →
              List.lookup (All.mapᶠ f pcs) i ≡ All.map f (List.lookup pcs i)
lookup-map (node x x₁) (here refl) = refl
lookup-map  {Q = Q} {f = f} (node x x₁) (there x₂ i) = begin
    lookup (All.map f (node x x₁)) (there x₂ i)      ≡⟨⟩
    lookup (node (f x) (All.mapᶠ f x₁)) (there x₂ i) ≡⟨⟩
    lookup (List.lookup (All.mapᶠ f x₁) x₂) i        ≡⟨ P.cong (λ x₄ → lookup x₄ i) (lookup-mapᶠ x₁ x₂) ⟩ 
    lookup (All.map f (List.lookup x₁ x₂)) i         ≡⟨ lookup-map (List.lookup x₁ x₂) i ⟩ 
    f (lookup (node x x₁) (there x₂ i))              ∎
lookup-mapᶠ {f = f} (px List.∷ pcs) (AnyList.here refl) = refl
lookup-mapᶠ {f = f} (px List.∷ pcs) (AnyList.there i) = begin
  List.lookup (All.mapᶠ f (px List.∷ pcs)) (AnyList.there i)             ≡⟨⟩
  List.lookup ((All.map f px) List.∷ (All.mapᶠ f pcs)) (AnyList.there i) ≡⟨⟩
  List.lookup (All.mapᶠ f pcs) i                                         ≡⟨ lookup-mapᶠ pcs i ⟩
  All.map f (List.lookup pcs i)                                          ≡⟨⟩
  All.map f (List.lookup (px List.∷ pcs) (AnyList.there i))              ∎

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for rose operations
------------------------------------------------------------------------
-- leaf

leaf⁺ : ∀ {x : A} → P x → All P (leaf x)
leaf⁺ px = node px List.[]

leaf⁻ : ∀ {x : A} → All P (leaf x) → P x
leaf⁻ (node px List.[]) = px

------------------------------------------------------------------------
-- root

root⁺ : All P t → P (Rose.root t)
root⁺ (node px _) = px

------------------------------------------------------------------------
-- children

children⁺ : All P t → Allᶠ P (Rose.children t)
children⁺ (node _ pxs) = pxs

------------------------------------------------------------------------
-- map

map⁺ : ∀ {f : A → B} → All (P ∘ f) t → All P (Rose.map f t)
mapᶠ⁺ : ∀ {f : A → B} → Allᶠ (P ∘ f) cs → Allᶠ P (Rose.mapᶠ f cs)
map⁺ (node r cs) = node r (mapᶠ⁺ cs)
mapᶠ⁺ List.[] = List.[]
mapᶠ⁺ (px List.∷ x) = (map⁺ px) List.∷ (mapᶠ⁺ x)

map⁻ : ∀ {f : A → B} → All P (Rose.map f t) → All (P ∘ f) t
mapᶠ⁻ : ∀ {f : A → B} → Allᶠ P (Rose.mapᶠ f cs) → Allᶠ (P ∘ f) cs
map⁻ (node x x₁) = node x (mapᶠ⁻ x₁)
mapᶠ⁻ {cs = []} List.[] = List.[]
mapᶠ⁻ {cs = c ∷ cs} (px List.∷ x) = map⁻ px List.∷ mapᶠ⁻ x

gmap : ∀ {f : A → B} → P ⋐ Q ∘ f → All P ⋐ All Q ∘ Rose.map f
gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- filter

module _ (P? : Decidable P) where

  all-filter : ∀ t → Maybe.All (All P) (filter P? t)
  all-filterᶠ : ∀ cs → Allᶠ P (filterᶠ P? cs)
  all-filter (node root₁ children₁) with P? root₁
  ... | yes pr = Maybe.just (node pr (all-filterᶠ children₁))
  ... | no ¬pr = Maybe.nothing
  all-filterᶠ [] = List.[]
  all-filterᶠ (node root₁ children₁ ∷ cs) with P? root₁ 
  ... | yes pr = (node pr (all-filterᶠ children₁)) List.∷ (all-filterᶠ cs)
  ... | no ¬pr = all-filterᶠ cs

  filter⁺ : All Q t → Maybe.All (All Q) (Rose.filter P? t)
  filterᶠ⁺ : Allᶠ Q cs → Allᶠ Q (filterᶠ P? cs)
  filter⁺ {t = node root₁ children₁} (node x x₁) with P? root₁
  ... | yes pr = Maybe.just (node x (filterᶠ⁺ x₁))
  ... | no ¬pr = Maybe.nothing
  filterᶠ⁺ {cs = []} ls = ls
  filterᶠ⁺ {cs = node root₁ children₁ ∷ cs} (x List.∷ xs) with P? root₁
  ... | yes pr = node (All.root x) (filterᶠ⁺ (All.children x)) List.∷ filterᶠ⁺ xs
  ... | no ¬pr = filterᶠ⁺ xs

  -- no elimination rule for filter, if there was such a rule it would look like:
  -- filterᶠ⁻ : Allᶠ Q (filterᶠ P? cs) → Allᶠ Q (filterᶠ (¬? ∘ P?) cs) → Allᶠ Q cs
  -- but subtrees of nodes that where removed by filter P? may still have nodes that are ¬P

------------------------------------------------------------------------
-- filterChildren

  all-filterChildren : ∀ r cs → P r → All P (filterChildren P? (node r cs))
  all-filterChildren r cs pr = node pr (all-filterᶠ cs)

  filterChildren⁺ : All Q t → All Q (filterChildren P? t)
  filterChildren⁺ (node x x₁) = node x (filterᶠ⁺ x₁)

  -- no elimination rule for filterChildren (see above)

------------------------------------------------------------------------
-- flatten

flatten⁺ : All P t → List.All P (flatten t)
flattenᶠ⁺ : Allᶠ P cs → List.All P (flattenᶠ cs)
flatten⁺ (node x x₁) = x List.∷ flattenᶠ⁺ x₁
flattenᶠ⁺ List.[] = List.[]
flattenᶠ⁺ (px List.∷ x) = AllList.++⁺ (flatten⁺ px) (flattenᶠ⁺ x)

flatten⁻ : List.All P (flatten t) → All P t
flattenᶠ⁻ : List.All P (flattenᶠ cs) → Allᶠ P cs
flatten⁻ (px List.∷ x) = node px (flattenᶠ⁻ x)
flattenᶠ⁻ {cs = []} x = List.[]
flattenᶠ⁻ {cs = c ∷ cs} (x) with AllList.++⁻ (flatten c) x 
... | fst , snd = flatten⁻ fst List.∷ flattenᶠ⁻ snd