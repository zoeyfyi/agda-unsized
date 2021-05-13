{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Properties where

open import Data.List using (List; []; _∷_)
import Data.List as List
open import Data.List.Extrema.Nat using (max)
open import Level using (Level)
open import Data.Nat
open import Relation.Nullary
open import Unsized.Data.Tree.Rose
open import Function.Base
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  variable
    ℓ : Level
    A B C : Set ℓ
    t t₁ t₂ : Rose A
    r r₁ r₂ : A
    cs cs₁ cs₂ : List (Rose A)
    
-----------------------------------------------------------------------
-- node

node-injective : node r₁ cs₁ ≡ node r₂ cs₂ → r₁ ≡ r₂ × cs₁ ≡ cs₂
node-injective refl = refl , refl

node-injectiveₗ : node r₁ cs₁ ≡ node r₂ cs₂ → r₁ ≡ r₂
node-injectiveₗ refl = refl

node-injectiveᵣ : node r₁ cs₁ ≡ node r₂ cs₂ → cs₁ ≡ cs₂
node-injectiveᵣ refl = refl

node-dec : Dec (r₁ ≡ r₂) → Dec (cs₁ ≡ cs₂) → Dec (node r₁ cs₁ ≡ node r₂ cs₂)
node-dec r₁≟r₂ cs₁≟cs₂ = Decidable.map′ (uncurry (cong₂ node)) node-injective (r₁≟r₂ ×-dec cs₁≟cs₂)

≡-dec : DecidableEquality A → DecidableEquality (Rose A)
≡-dec' : DecidableEquality A → DecidableEquality (List (Rose A))
≡-dec _≟_ (node root₁ children₁) (node root₂ children₂) = node-dec (root₁ ≟ root₂) (≡-dec' _≟_ children₁ children₂)
≡-dec' _≟_ [] [] = yes refl
≡-dec' _≟_ [] (_ ∷ _) = no (λ ())
≡-dec' _≟_ (_ ∷ _) [] = no (λ ())
≡-dec' _≟_ (c₁ ∷ cs₁) (c₂ ∷ cs₂) = List.∷-dec (≡-dec _≟_ c₁ c₂) (≡-dec' _≟_ cs₁ cs₂)
    
------------------------------------------------------------------------
-- map properties

map-compose : (f : A → B) (g : B → C) → map (g ∘ f) ≗ map g ∘ map f
map'-compose : (f :  A → B) (g : B → C) → map' (g ∘ f) ≗ map' g ∘ map' f

map-compose f g (node r []) = refl
map-compose f g (node r (c ∷ cs)) = cong (node (g (f r))) $ begin
  map (g ∘ f) c ∷ map' (g ∘ f) cs          ≡⟨ cong₂ _∷_ (map-compose f g c) (map'-compose f g cs) ⟩
  (map g ∘ map f) c ∷ (map' g ∘ map' f) cs ∎

map'-compose f g [] = refl
map'-compose f g (t ∷ ts) = begin
  map (g ∘ f) t ∷ map' (g ∘ f) ts          ≡⟨ cong₂ _∷_ (map-compose f g t) (map'-compose f g ts) ⟩
  (map g ∘ map f) t ∷ (map' g ∘ map' f) ts ≡⟨⟩
  (map' g ∘ map' f) (t ∷ ts)               ∎

depth-map : (f : A → B) (t : Rose A) → depth (map f t) ≡ depth t
depth'-map : (f : A → B) (ts : List (Rose A)) → depth' (map' f ts) ≡ depth' ts

depth-map f (node root₁ children₁) = cong suc $ begin
  depth' (map' f children₁) ≡⟨ depth'-map f children₁ ⟩
  depth' children₁          ∎

depth'-map f [] = refl
depth'-map f (t ∷ ts) = begin 
    depth (map f t) ⊔ depth' (map' f ts) ≡⟨ cong₂ _⊔_ (depth-map f t) (depth'-map f ts) ⟩ 
    depth t ⊔ depth' ts                  ∎

------------------------------------------------------------------------
-- foldr properties

foldr-map : (f : A → B) (n : B → List C → C) (ts : Rose A) →
            foldr n (map f ts) ≡ foldr (n ∘ f) ts
foldr'-map : (f : A → B) (n : B → List C → C) (ts : List (Rose A)) →
             foldr' n (map' f ts) ≡ foldr' (n ∘ f) ts 

foldr-map f n (node root₁ children₁) = cong (n (f root₁)) $ begin
  foldr' n (map' f children₁) ≡⟨ foldr'-map f n children₁ ⟩
  foldr' (n ∘ f) children₁    ∎

foldr'-map f n [] = refl
foldr'-map f n (t ∷ ts) = begin
  foldr n (map f t) ∷ foldr' n (map' f ts) ≡⟨ cong₂ _∷_ (foldr-map f n t) (foldr'-map f n ts) ⟩ 
  foldr (n ∘ f) t ∷ foldr' (n ∘ f) ts      ∎
