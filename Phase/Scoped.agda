
module Phase.Scoped where

open import Data.List using (List; _++_; _∷_)
open import Data.String using (String) renaming (_++_ to _++s_)
open import Data.Integer using (ℤ)

open import Name
open import Position
open import Thinning using (_∈_)

private variable
  n c : Name
  Γ Δ : List Name

data Patₛ (Δ : List Name) : Set where
  Tagged : (p : Pos) (ctor : String) (args : List (Patₛ Δ)) → Patₛ Δ
  Var    : (p : Pos) (ptr : n ∈ Δ) → Patₛ Δ
  Int    : (p : Pos) (int : ℤ) → Patₛ Δ
  Str    : (p : Pos) (str : String) → Patₛ Δ
  Wild   : (p : Pos) → Patₛ Δ

open import Phase.Raw

mutual
  data Exprₛ (Γ : List Name) : Set where
    Var : (p : Pos) (ptr : n ∈ Γ) → Exprₛ Γ

    Lam : (p : Pos) (body : Exprₛ (Δ ++ Γ)) → Exprₛ Γ
    App : (p : Pos) (fun : Exprₛ Γ) (args : List (Exprₛ Γ)) → Exprₛ Γ

    Let : (p : Pos) (value : Exprₛ Γ) (context : Exprₛ (n ∷ Γ)) → Exprₛ Γ
    Fix : (p : Pos) (fixpoint : Exprₛ (n ∷ Γ)) → Exprₛ Γ

    Int : (p : Pos) (int : ℤ) → Exprₛ Γ
    Str : (p : Pos) (str : String) → Exprₛ Γ

    Tagged : (p : Pos) (ctor : String) (args : List (Exprₛ Γ)) → Exprₛ Γ
    Match : (p : Pos) (subj : Exprₛ Γ) (alts : List (Altₛ Γ)) → Exprₛ Γ

    Reflect : (p : Pos) (expr : Exprᵣ) → Exprₛ Γ
    Reify : (p : Pos) (expr : Exprₛ Γ) → Exprₛ Γ
    Error : (p : Pos) (msg : String) (payload : Exprₛ Γ) → Exprₛ Γ

  record Altₛ (Γ : List Name) : Set where
    inductive
    constructor Case
    field
      p       : Pos
      {scope} : List Name
      pat     : Patₛ scope
      body    : Exprₛ (scope ++ Γ)

open import Either

data ScopeError : Set where
  Undefined : (p : Pos) → Name → ScopeError

showScopeError : ScopeError → String
showScopeError (Undefined p n) = "name " ++s showName n ++s " is not defined, at " ++s showPos p
