{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Unsized.Data.Tree.Rose.Membership.Propositional {ℓ} {A : Set ℓ} where

open import Unsized.Data.Tree.Rose.Relation.Unary.Any using (Any)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; setoid; subst)

import Unsized.Data.Tree.Rose.Membership.Setoid as SetoidMembership

------------------------------------------------------------------------
-- Re-export contents of setoid membership

open SetoidMembership (setoid A) public hiding (lose)
