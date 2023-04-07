
module Position where

open import Data.String using (String; _++_)
open import Data.Maybe using (just; nothing) public
open import Data.Nat.Show

open import Lisp.Grammar.ASTLisp using (#BNFCPosition; #pair; #intToNat)

open import Pretty

Pos : Set
Pos = #BNFCPosition

showPos : Pos → String
showPos (just (#pair x x₁)) = blue (show (#intToNat x) ++ ":" ++ show (#intToNat x₁))
showPos nothing = blue "-:-"
