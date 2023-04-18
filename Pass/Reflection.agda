
module Pass.Reflection where

open import Phase.Raw
open import Phase.Evaluated
open import Name
open import Data.List using (List; []; _∷_; [_]; map)
open import Position
open import Either


ofList : Pos → Value → List Value ⊎ EvalError
ofList p (Tagged "Nil" []) = ⦇ [] ⦈
ofList p (Tagged "Cons" (x ∷ xs ∷ [])) = ⦇ pure x ∷ ofList p xs ⦈
ofList p val = fail (UserError p "ofList: expected a reflected list, not: " val)

asList : List Value → Value
asList [] = Tagged "Nil" []
asList (x ∷ vals) = Tagged "Cons" (x ∷ asList vals ∷ [])

reflectName : Name → Value
reflectName (♯ name) = Str name

mutual
  {-# TERMINATING #-}
  reflect : Exprᵣ → Value
  reflect (Var p₁ name) = Tagged "Var" [ reflectName name ]
  reflect (Lam p₁ args prog) = Tagged "Lam" (asList (map reflectName args) ∷ reflect prog ∷ [])
  reflect (App p₁ prog args) = Tagged "App" (reflect prog ∷ asList (map reflect args) ∷ [])
  reflect (Let p₁ var prog prog₁) = Tagged "Let" (reflectName var ∷ reflect prog ∷ reflect prog₁ ∷ [])
  reflect (Fix p₁ var prog) = Tagged "Fix" (reflectName var ∷ reflect prog ∷ [])
  reflect (Int p₁ int) = Tagged "Int" [ Int int ]
  reflect (Str p₁ str) = Tagged "Str" [ Str str ]
  reflect (Tagged p₁ ctor args) = Tagged "Tagged" (Str ctor ∷ asList (map reflect args) ∷ [])
  reflect (Match p₁ prog alts) = Tagged "Match" (reflect prog ∷ asList (map reflectAlt alts) ∷ [])
  reflect (Reflect p expr) = Tagged "Reflect" [ reflect expr ]
  reflect (Reify p expr) = Tagged "Reify" [ reflect expr ]
  reflect (Error p msg expr) = Tagged "Error" (Str msg ∷ reflect expr ∷ [])

  reflectAlt : Altᵣ → Value
  reflectAlt (Case p pat₁ body) =
    Tagged "Case" (reflectPat pat₁ ∷ reflect body ∷ [])

  reflectPat : Patᵣ → Value
  reflectPat (Tagged p ctor args) = Tagged "Tagged" (Str ctor ∷ asList (map reflectPat args) ∷ [])
  reflectPat (Var p name) = Tagged "Var" [ reflectName name ]
  reflectPat (Int p int) = Tagged "Int" [ Int int ]
  reflectPat (Str p str) = Tagged "Str" [ Str str ]
  reflectPat (Wild p) = Tagged "Wild" []


reifyName : Pos → Value → Name ⊎ EvalError
reifyName p (Str name) = ⦇ (♯ name) ⦈
reifyName p val = fail (UserError p "reifyName: expected string, not:" val)

mutual
  {-# TERMINATING #-}
  reify : Pos → Value → Exprᵣ ⊎ EvalError
  reify p (Tagged "Var" (Str name ∷ [])) = ⦇ (Var p (♯ name)) ⦈
  reify p (Tagged "Lam" (args ∷ body ∷ [])) = do
    args ← ofList p args
    args ← each (reifyName p) args
    ⦇ (Lam p args) (reify p body) ⦈

  reify p (Tagged "App" (f ∷ xs ∷ [])) = do
    xs ← ofList p xs
    ⦇ (App p) (reify p f) (each (reify p) xs) ⦈

  reify p (Tagged "Let" (n ∷ x ∷ body ∷ [])) = ⦇ (Let p) (reifyName p n) (reify p x) (reify p body) ⦈
  reify p (Tagged "Fix" (n ∷ body ∷ [])) = ⦇ (Fix p) (reifyName p n) (reify p body) ⦈
  reify p (Tagged "Int" (Int int ∷ [])) = ⦇ (Int p int) ⦈
  reify p (Tagged "Str" (Str str ∷ [])) = ⦇ (Str p str) ⦈
  reify p (Tagged "Tagged" (Str ctor ∷ values ∷ [])) = do
    values ← ofList p values
    ⦇ (Tagged p ctor) (each (reify p) values) ⦈

  reify p (Tagged "Match" (subj ∷ alts ∷ [])) = do
    alts ← ofList p alts
    ⦇ (Match p) (reify p subj) (each (reifyAlt p) alts) ⦈

  reify p (Tagged "Reflect" (expr ∷ [])) = ⦇ (Reflect p) (reify p expr) ⦈
  reify p (Tagged "Reify"   (expr ∷ [])) = ⦇ (Reify p) (reify p expr) ⦈
  reify p (Tagged "Error"   (Str msg ∷ expr ∷ [])) = ⦇ (Error p msg) (reify p expr) ⦈

  reify p other = fail (UserError p "reify: expected reflected expression, not this:" other)


  reifyAlt : Pos → Value → Altᵣ ⊎ EvalError
  reifyAlt p (Tagged "Case" (pat ∷ body ∷ [])) = ⦇ (Case p) (reifyPat p pat) (reify p body) ⦈
  reifyAlt p val = fail (UserError p "reify: expected reflected case-alt, not this:" val)

  reifyPat : Pos → Value → Patᵣ ⊎ EvalError
  reifyPat p (Tagged "Tagged" (Str ctor ∷ pats ∷ [])) = do
    pats ← ofList p pats
    ⦇ (Tagged p ctor) (each (reifyPat p) pats) ⦈

  reifyPat p (Tagged "Var" (Str name ∷ [])) = ⦇ (Var p (♯ name)) ⦈
  reifyPat p (Tagged "Int" (Int int ∷ [])) = ⦇ (Int p int) ⦈
  reifyPat p (Tagged "Str" (Str str ∷ [])) = ⦇ (Str p str) ⦈
  reifyPat p (Tagged "Wild" []) = ⦇ (Wild p) ⦈
  reifyPat p pat = fail (UserError p "reify: expected reflected program, not this:" pat)