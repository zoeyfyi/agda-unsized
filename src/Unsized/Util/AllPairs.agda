{-# OPTIONS --without-K --safe #-}

module Unsized.Util.AllPairs where

open import Data.List hiding (any)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Function.Base using (_∘_; flip)
open import Level using (Level)
open import Relation.Binary using (Rel; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (does)

private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

module _ {R : Rel A ℓ} {f : B → A} where

  map⁻ : ∀ {xs} → AllPairs R (map f xs) → 
         AllPairs (λ x y → R (f x) (f y)) xs
  map⁻ {[]} _ = []
  map⁻ {x ∷ xs} (x∈xs ∷ xs!) = (All.map⁻ x∈xs) ∷ (map⁻ xs!)  
