
module Pass.FromBNFC where

open import Data.List using (map; foldr; []; _∷_)
open import Data.Integer using (-_; ℤ)
open import Data.String using (fromList)

open import Lisp.Grammar.ASTLisp

open import Phase.Raw
open import Name
open import Position

nameᵣ : Lisp.Grammar.ASTLisp.Name → Name.Name
nameᵣ (name x) = ♯ x

mutual
  {-# TERMINATING #-}
  exprᵣ : Expr → Exprᵣ
  exprᵣ (var p x) = Var p (nameᵣ x)
  exprᵣ (lam p xs expr) = Lam p (map nameᵣ xs) (exprᵣ expr)
  exprᵣ (app p expr es) = App p (exprᵣ expr) (map exprᵣ es)
  exprᵣ (let' p x expr expr₁) = Let p (nameᵣ x) (exprᵣ expr) (exprᵣ expr₁)
  exprᵣ (fix p x expr) = Fix p (nameᵣ x) (exprᵣ expr)
  exprᵣ (int p x) = Int p x
  exprᵣ (neg p x) = Int p (- x)
  exprᵣ (str p x) = Str p (Data.String.fromList x)
  exprᵣ (tag p (symbol x) es) = Tagged p x (map exprᵣ es)
  exprᵣ (mtc p expr as) = Match p (exprᵣ expr) (map altᵣ as)
  exprᵣ (lst p es) = foldr (λ x x₁ → Tagged p "Cons" ( exprᵣ x ∷ x₁ ∷ [])) (Tagged p "Nil" []) es
  exprᵣ (spl p es expr) = foldr (λ x x₁ → Tagged p "Cons" ( exprᵣ x ∷ x₁ ∷ [])) (exprᵣ expr) es

  altᵣ : Alt → Altᵣ
  altᵣ (cas p₁ p₂ e) = Case p₁ (patᵣ p₂) (exprᵣ e)

  patᵣ : Pat → Patᵣ
  patᵣ (pTag p (symbol x) ps) = Tagged p x (map patᵣ ps)
  patᵣ (pVar p (name x)) = Var p (♯ x)
  patᵣ (pInt p x) = Int p x
  patᵣ (pNeg p x) = Int p (- x)
  patᵣ (pStr p x) = Str p (Data.String.fromList x)
  patᵣ (pWld p) = Wild p
  patᵣ (pLst p ps) = foldr (λ x x₁ → Tagged p "Cons" ( patᵣ x ∷ x₁ ∷ [])) (Tagged p "Nil" []) ps
  patᵣ (pSpl p ps pat) = foldr (λ x x₁ → Tagged p "Cons" ( patᵣ x ∷ x₁ ∷ [])) (patᵣ pat) ps

startᵣ : Start → Exprᵣ
startᵣ (s p e) = exprᵣ e