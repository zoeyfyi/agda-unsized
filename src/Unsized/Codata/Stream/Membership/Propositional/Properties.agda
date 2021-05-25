{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Membership.Propositional.Properties where

open import Level
open import Data.List using (List)
import Data.List.Membership.Propositional as L
import Data.List.Relation.Unary.Any as L
open import Unsized.Codata.Stream
open import Unsized.Codata.Stream.Relation.Unary.Any
open import Unsized.Codata.Stream.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Data.Sum

private
  variable
    a : Level
    A : Set a
    ls : List A
    xs : Stream A
    
------------------------------------------------------------------------
-- repeat

repeat-∈ : ∀ {x : A} → x ∈ repeat x
repeat-∈ = here refl

------------------------------------------------------------------------
-- _++_

∈-++⁺ˡ : ∀ {x} → x L.∈ ls → x ∈ (ls ++ xs) 
∈-++⁺ˡ (L.here refl) = here refl
∈-++⁺ˡ (L.there x) = there (∈-++⁺ˡ x)

∈-++⁺ʳ : ∀ {x} → x ∈ xs → x ∈ (ls ++ xs)
∈-++⁺ʳ {ls = List.[]} (here refl) = here refl
∈-++⁺ʳ {ls = List.[]} (there x∈xs) = there x∈xs
∈-++⁺ʳ {ls = x List.∷ ls} x∈xs = there (∈-++⁺ʳ x∈xs)

∈-++⁻ : ∀ {x} → x ∈ (ls ++ xs) → (x L.∈ ls) ⊎ (x ∈ xs)
∈-++⁻ {ls = List.[]} (here refl) = inj₂ (here refl)
∈-++⁻ {ls = List.[]} (there x) = inj₂ (there x)
∈-++⁻ {ls = l List.∷ ls} (here refl) = inj₁ (L.here refl)
∈-++⁻ {ls = l List.∷ ls} (there x) with ∈-++⁻ x
... | inj₁ ∈ls = inj₁ (L.there ∈ls)
... | inj₂ ∈xs = inj₂ ∈xs
