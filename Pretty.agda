
module Pretty where

open import Data.String using (String; _++_; lines; unlines; intersperse)
open import Data.Nat
open import Data.Nat.Show
open import Data.List using ([]; _∷_; map)
open import Function using (_∘_)

color : ℕ → String → String
color c str = ("\x1B[" ++ show (30 + c) ++ "m") ++ str ++ "\x1B[0m"

br : String → String
br str = ("\x1B[1m") ++ str ++ "\x1B[0m"

red green yellow blue magenta cyan : String → String
red     = color 1
green   = color 2
yellow  = color 3
blue    = color 4
magenta = color 5
cyan    = color 6

indent : String → String
indent str with lines str
... | []     = ""
... | x ∷ [] = x
... | xs     = intersperse "\n  " xs

indent! : String → String
indent! = unlines ∘ map ("  " ++_) ∘ lines
