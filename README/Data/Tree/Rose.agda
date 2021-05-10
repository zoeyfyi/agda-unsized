{-# OPTIONS --without-K --safe #-}

module README.Data.Tree.Rose where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unsized.Data.Tree.Rose
open import Unsized.Data.Tree.Rose.Show using (display)
open import Level
open import Data.List
open import Data.String

private
  variable
    ℓ : Level
    A : Set ℓ

tree : Rose (List String)
tree = node [ "one" ]
      ( node [ "two" ] []
      ∷ node ("three" ∷ "and" ∷ "four" ∷ [])
        ( node [ "five" ] []
        ∷ node [ "six" ] (node [ "seven" ] [] ∷ [])
        ∷ node [ "eight" ] []
        ∷ [])
      ∷ node [ "nine" ]
        ( node [ "ten" ] []
        ∷ node [ "eleven" ] [] ∷ [])
        ∷ [])

_ : unlines (display tree) ≡ "one
\   \ ├ two
\   \ ├ three
\   \ │ and
\   \ │ four
\   \ │  ├ five
\   \ │  ├ six
\   \ │  │  └ seven
\   \ │  └ eight
\   \ └ nine
\   \    ├ ten
\   \    └ eleven"
_ = refl