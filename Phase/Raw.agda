
module Phase.Raw where

open import Data.String using (String; _++_; lines; intersperse; unlines; unwords) renaming (show to show𝕊)
open import Data.List using (List; _∷_; []; map)
open import Data.Integer using (-_; ℤ)
open import Data.Integer.Show
open import Function using (_∘_)

open import Position
open import Name
open import Pretty

data Patᵣ : Set where
  Tagged : (p : Pos) (ctor : String) (args : List Patᵣ) → Patᵣ
  Var    : (p : Pos) (name : Name) → Patᵣ
  Int    : (p : Pos) (int : ℤ) → Patᵣ
  Str    : (p : Pos) (str : String) → Patᵣ
  Wild   : (p : Pos) → Patᵣ

mutual
  data Exprᵣ : Set where
    Var    : (p : Pos) (name : Name) → Exprᵣ
    Lam    : (p : Pos) (args : List Name) (body : Exprᵣ) → Exprᵣ
    App    : (p : Pos) (fun : Exprᵣ) (args : List Exprᵣ) → Exprᵣ
    Let    : (p : Pos) (var : Name) (value : Exprᵣ) (body : Exprᵣ) → Exprᵣ
    Fix    : (p : Pos) (var : Name) (fixpoint : Exprᵣ) → Exprᵣ
    Int    : (p : Pos) (int : ℤ) → Exprᵣ
    Str    : (p : Pos) (str : String) → Exprᵣ
    Tagged : (p : Pos) (ctor : String) (args : List Exprᵣ) → Exprᵣ
    Match  : (p : Pos) (subj : Exprᵣ) (alts : List Altᵣ) → Exprᵣ
    Reflect : (p : Pos) (expr : Exprᵣ) → Exprᵣ
    Reify : (p : Pos) (expr : Exprᵣ) → Exprᵣ
    Error : (p : Pos) (msg : String) (payload : Exprᵣ) → Exprᵣ

  record Altᵣ : Set where
    inductive
    constructor Case
    field
      p    : Pos
      pat  : Patᵣ
      body : Exprᵣ

open import Either
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

exprIsList : Exprᵣ → List Exprᵣ ⊎ (List Exprᵣ × Exprᵣ) ⊎ ⊤
exprIsList (Tagged p "Nil" []) = inj₁ []
exprIsList (Tagged p "Cons" (x ∷ xs ∷ [])) with exprIsList xs
... | inj₁ a = inj₁ (x ∷ a)
... | inj₂ (inj₁ (xs , b)) = inj₂ (inj₁ (x ∷ xs , b))
... | inj₂ (inj₂ tt) = inj₂ (inj₁ (x ∷ [] , xs))
exprIsList value = inj₂ (inj₂ _)

patIsList : Patᵣ → List Patᵣ ⊎ (List Patᵣ × Patᵣ) ⊎ ⊤
patIsList (Tagged p "Nil" []) = inj₁ []
patIsList (Tagged p "Cons" (x ∷ xs ∷ [])) with patIsList xs
... | inj₁ a = inj₁ (x ∷ a)
... | inj₂ (inj₁ (xs , b)) = inj₂ (inj₁ (x ∷ xs , b))
... | inj₂ (inj₂ tt) = inj₂ (inj₁ (x ∷ [] , xs))
patIsList value = inj₂ (inj₂ _)

mutual
  {-# TERMINATING #-}
  showExprᵣ : Exprᵣ → String
  showExprᵣ (Var p name) = showName name
  showExprᵣ (Lam p args expr) =
    let args₁ = intersperse ", " (map showName args) in
    cyan "fun " ++ args₁ ++ cyan " ->\n" ++ indent! (showExprᵣ expr) ++ cyan "\nend"

  showExprᵣ (App p expr args) = showExprᵣ expr ++ "(" ++ intersperse ", " (map showExprᵣ args) ++ ")"
  showExprᵣ (Let p var expr expr₁) = green "let " ++ showName var ++ green " = " ++ showExprᵣ expr ++ green ";\n\n" ++ showExprᵣ expr₁
  showExprᵣ (Fix p var expr) = red "fix " ++ showName var ++ red " ->\n" ++ indent! (showExprᵣ expr) ++ red "\nend"
  showExprᵣ (Int p int) = red (Data.Integer.Show.show int)
  showExprᵣ (Str p str) = blue (Data.String.show str)
  showExprᵣ (Match p expr alts) = cyan "case " ++ showExprᵣ expr ++ cyan " of\n" ++ indent! (unlines (map showAltᵣ alts)) ++ cyan "\nend"
  showExprᵣ expr@(Tagged p ctor args) with exprIsList expr
  ... | inj₁ a = blue "[" ++ intersperse (blue ", ") (map showExprᵣ a) ++ blue "]"
  ... | inj₂ (inj₁ (a , b)) = blue "[" ++ intersperse (blue ", ") (map showExprᵣ a) ++ blue ", ..." ++ showExprᵣ b ++ blue "]"
  ... | _ = magenta ctor ++ " {" ++ intersperse ", " (map showExprᵣ args) ++ "}"
  showExprᵣ (Reflect p expr) = "'" ++ showExprᵣ expr
  showExprᵣ (Reify p expr) = "!" ++ showExprᵣ expr
  showExprᵣ (Error p msg expr) = "error " ++ show𝕊 msg ++ " " ++ showExprᵣ expr

  showAltᵣ : Altᵣ → String
  showAltᵣ (Case p pat body) = showPatᵣ pat ++ " ->\n" ++ indent! (showExprᵣ body) ++ ";"

  showPatᵣ : Patᵣ → String
  showPatᵣ (Var p var) = showName var
  showPatᵣ (Int p int) = red (Data.Integer.Show.show int)
  showPatᵣ (Str p str) = blue (Data.String.show str)
  showPatᵣ (Wild p)    = cyan "_"
  showPatᵣ pat@(Tagged p ctor args) with patIsList pat
  ... | inj₁ a = blue "[" ++ intersperse (blue ", ") (map showPatᵣ a) ++ blue "]"
  ... | inj₂ (inj₁ (a , b)) = blue "[" ++ intersperse (blue ", ") (map showPatᵣ a) ++ blue ", ..." ++ showPatᵣ b ++ blue "]"
  ... | _ = magenta ctor ++ " {" ++ intersperse ", " (map showPatᵣ args) ++ "}"
