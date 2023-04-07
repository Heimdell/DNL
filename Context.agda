
module Context where

open import Data.List using (List)
open import Data.Product using (_×_)

open import Name

Ctx : (T : Set) → Set
Ctx T = List (Name × T)