
module Name where

open import Data.String using (String)
open import Pretty

record Name : Set where
  constructor ♯
  field
    name : String

showName : Name → String
showName (♯ name) = yellow name