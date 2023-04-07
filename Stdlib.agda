
module Stdlib where

open import Data.Integer using (_+_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Phase.Evaluated

open import Either
open import Position
open import Name

add : Pos → Ctx (♯ "x" ∷ ♯ "y" ∷ []) → Value ⊎ EvalError
add p (Int x ∷ Int y ∷ []) = inj₁ (Int (x + y))
add p (x ∷ y ∷ []) = inj₂ (Expected2Ints p x y)

mutual
  cmpValues : Pos → Value → Value → Value ⊎ EvalError
  cmpValues p (Lam action) y = inj₂ (CantCompareFunctions p)
  cmpValues p x (Lam action) = inj₂ (CantCompareFunctions p)
  cmpValues p (Int x) (Int y) with x Data.Integer.≟ y | x Data.Integer.<? y
  ... | yes refl | v     = inj₁ (Tagged "Equal" [])
  ... | no  nope | yes _ = inj₁ (Tagged "Less" [])
  ... | no  nope | no  _ = inj₁ (Tagged "Greater" [])

  cmpValues p (Str x) (Str y) with x Data.String.≟ y | x Data.String.<? y
  ... | yes refl | v     = inj₁ (Tagged "Equal" [])
  ... | no  nope | yes _ = inj₁ (Tagged "Less" [])
  ... | no  nope | no  _ = inj₁ (Tagged "Greater" [])

  cmpValues p (Tagged ctor args) (Tagged ctor₁ args₁) with ctor Data.String.≟ ctor₁ | ctor Data.String.<? ctor₁
  ... | no  nope | yes _ = inj₁ (Tagged "Less" [])
  ... | no  nope | no  _ = inj₁ (Tagged "Greater" [])
  ... | yes refl | v with cmpLists p ctor args args₁
  ... | inj₂ (SameTagDifferInArgCount _ _ _ _) = inj₂ (SameTagDifferInArgCount p ctor args args₁)
  ... | other                                  = other


  cmpValues p x y = inj₂ (CantCompareValueOfDifferentTypes p x y)


  cmpLists : Pos → String → List Value → List Value → Value ⊎ EvalError
  cmpLists p s [] [] = inj₁ (Tagged "Equal" [])
  cmpLists p s [] (x ∷ ys) = inj₂ (SameTagDifferInArgCount p s [] [])
  cmpLists p s (x ∷ xs) [] = inj₂ (SameTagDifferInArgCount p s [] [])
  cmpLists p s (x ∷ xs) (x₁ ∷ ys) with cmpValues p x x₁
  ... | inj₁ (Tagged "Equal" []) = cmpLists p s xs ys
  ... | other                    = other

cmp : Pos → Ctx (♯ "x" ∷ ♯ "y" ∷ []) → Value ⊎ EvalError
cmp p (x ∷ y ∷ []) = cmpValues p x y
