
module Pass.ToScoped where

open import Data.List using (List; _++_; _∷_; []; map; [_])
open import Data.String using ()
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Position
open import Name
open import Thinning using (_∈_; 𝟙∷; 𝟘∷; 𝟘⋯)
open import Either

open import Phase.Raw
open import Phase.Scoped

private variable
  Γ Δ : List Name

findName : (p : Pos) (n : Name) {Γ : List Name} → n ∈ Γ ⊎ ScopeError
findName p n {[]} = fail (Undefined p n)
findName p (♯ n) {♯ x ∷ Γ} with n Data.String.≟ x
... | yes refl = ⦇ (𝟙∷ 𝟘⋯) ⦈
... | no  _    = ⦇ 𝟘∷ (findName p (♯ n)) ⦈

{-# TERMINATING #-}
mutual
  checkₛ : Exprᵣ → Exprₛ Γ ⊎ ScopeError
  checkₛ (Var p name)           = ⦇ (Var p) (findName p name) ⦈
  checkₛ (Lam p args expr)      = ⦇ (Lam {Δ = args} p) (checkₛ expr) ⦈
  checkₛ (App p expr args)      = ⦇ (App p) (checkₛ expr) (each checkₛ args) ⦈
  checkₛ (Let p var expr expr₁) = ⦇ (Let {n = var} p) (checkₛ expr) (checkₛ expr₁) ⦈
  checkₛ (Fix p var expr)       = ⦇ (Fix {n = var} p) (checkₛ expr) ⦈
  checkₛ (Int p int)            = ⦇ (Int p int) ⦈
  checkₛ (Str p str)            = ⦇ (Str p str) ⦈
  checkₛ (Tagged p ctor args)   = ⦇ (Tagged p ctor) (each checkₛ args) ⦈
  checkₛ (Match p expr alts)    = ⦇ (Match p) (checkₛ expr) (each checkAltₛ alts) ⦈

  checkAltₛ : Altᵣ → Altₛ Γ ⊎ ScopeError
  checkAltₛ (Case p pat body) = do
    let Δ = patNames pat
    pat  ← checkPatₛ pat
    body ← checkₛ body
    pure (Case p {scope = Δ} pat body)

  patNames : Patᵣ → List Name
  patNames (Tagged p x x₁) = Data.List.foldr _++_ [] (map patNames x₁)
  patNames (Var p name)    = [ name ]
  patNames (Int p _)       = []
  patNames (Str p _)       = []
  patNames (Wild _)        = []

  checkPatₛ : Patᵣ → Patₛ Δ ⊎ ScopeError
  checkPatₛ (Tagged p ctor args) = ⦇ (Tagged p ctor) (each checkPatₛ args) ⦈
  checkPatₛ (Var p name)         = ⦇ (Var p) (findName p name) ⦈
  checkPatₛ (Int p int)          = ⦇ (Int p int) ⦈
  checkPatₛ (Str p str)          = ⦇ (Str p str) ⦈
  checkPatₛ (Wild p)             = ⦇ (Wild p) ⦈
