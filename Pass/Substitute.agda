
module Pass.Substitute where

open import Data.List using (List; _++_; _∷_; []; map)

open import Phase.Scoped
open import Thinning
open import Name

private variable
  Γ Δ Ε : List Name

mutual
  {-# TERMINATING #-}
  _⊢_ : Γ ⊂ Δ → Exprₛ Γ → Exprₛ Δ
  sub ⊢ Var p ptr = Var p (ptr ∙ sub)
  sub ⊢ Lam p expr = Lam p (𝟙⋯𝟙 sub ⊢ expr)
  sub ⊢ App p expr args = App p (sub ⊢ expr) (map (sub ⊢_) args)
  sub ⊢ Let p expr expr₁ = Let p (sub ⊢ expr) (𝟙⋯𝟙 sub ⊢ expr₁)
  sub ⊢ Fix p expr = Fix p (𝟙⋯𝟙 sub ⊢ expr)
  sub ⊢ Int p int = Int p int
  sub ⊢ Str p str = Str p str
  sub ⊢ Tagged p ctor args = Tagged p ctor (map (sub ⊢_) args)
  sub ⊢ Match p expr alts = Match p (sub ⊢ expr) (map (sub ⊢alt_) alts)

  _⊢alt_ : Γ ⊂ Δ → Altₛ Γ → Altₛ Δ
  sub ⊢alt Case p pat body = Case p pat (𝟙⋯𝟙 sub ⊢ body)
