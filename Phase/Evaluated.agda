
module Phase.Evaluated where

open import Data.List using (List; map; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _++_; intersperse; unwords)
import Data.Integer.Show

open import Name
open import Position
open import Either
open import Pretty

private variable
  Γ Δ : List Name

open import Phase.Scoped using (ScopeError; showScopeError)

mutual
  data EvalError : Set where
    TooMuchArgs       : (p : Pos) (formal : List Name) (args : List Value) → EvalError
    NotEnoughArgs     : (p : Pos) (formal : List Name) (args : List Value) → EvalError
    NonFunctionCalled : (p : Pos) (func : Value) → EvalError
    MatchFailed       : (p : Pos) (subj : Value) → EvalError
    Expected2Ints     : (p : Pos) (x : Value) (y : Value) → EvalError
    OnlyFunctionsCanRecure : (p : Pos) → EvalError
    CantCompareFunctions : (p : Pos) → EvalError
    CantCompareValueOfDifferentTypes : (p : Pos) (x : Value) (y : Value) → EvalError
    SameTagDifferInArgCount : (p : Pos) (t : String) (xs ys : List Value) → EvalError
    UserError : (p : Pos) → String → (v : Value) → EvalError
    ReifyError : ScopeError → EvalError

  {-# NO_POSITIVITY_CHECK #-}
  data Value : Set where
    Lam    : (action : Pos → Ctx Δ → Value ⊎ EvalError) → Value
    Int    : (int : ℤ) → Value
    Str    : (str : String) → Value
    Tagged : (ctor : String) (args : List Value) → Value

  Ctx : List Name → Set
  Ctx Γ = All (λ _ → Value) Γ

open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

valueIsList : Value → List Value ⊎ (List Value × Value) ⊎ ⊤
valueIsList (Tagged "Nil" []) = inj₁ []
valueIsList (Tagged "Cons" (x ∷ xs ∷ [])) with valueIsList xs
... | inj₁ a = inj₁ (x ∷ a)
... | inj₂ (inj₁ (xs , b)) = inj₂ (inj₁ (x ∷ xs , b))
... | inj₂ (inj₂ tt) = inj₂ (inj₁ (x ∷ [] , xs))
valueIsList value = inj₂ (inj₂ _)

{-# TERMINATING #-}
showValue : Value → String
showValue (Lam action) = green "<function>"
showValue (Int int) = red (Data.Integer.Show.show int)
showValue (Str str) = cyan (Data.String.show str)
showValue val@(Tagged ctor args) with valueIsList val
... | inj₁ list = blue "[" ++ intersperse (blue ",") (map showValue list) ++ blue "]"
... | inj₂ (inj₁ (list , last)) = blue "[" ++ intersperse (blue ",") (map showValue list) ++ blue ", ..." ++ showValue last ++ blue "]"
... | inj₂ (inj₂ _) = magenta ctor ++ " {" ++ intersperse ", " (map showValue args) ++ "}"

showValue' : ℕ → Value → String
showValue' zero (Lam action) = green "<function>"
showValue' zero (Int int) = red (Data.Integer.Show.show int)
showValue' zero (Str str) = cyan (Data.String.show str)
showValue' zero (Tagged ctor args) = magenta ctor ++ "(...)"
showValue' (suc n) (Lam action) = green "<function>"
showValue' (suc n) (Int int) = red (Data.Integer.Show.show int)
showValue' (suc n) (Str str) = cyan (Data.String.show str)
showValue' (suc n) (Tagged ctor args) = magenta ctor ++ " {" ++ intersperse ", " (map (showValue' n) args) ++ "}"

showEvalError : EvalError → String
showEvalError (TooMuchArgs p formal args) =
  "too much arguments; for list " ++ unwords (map showName formal)
  ++ " it is given " ++ unwords (map (showValue' 2) args)
  ++ ", at " ++ showPos p

showEvalError (NotEnoughArgs p formal args) =
  "not enough arguments; for list " ++ unwords (map showName formal)
  ++ " it is given " ++ unwords (map (showValue' 2) args)
  ++ ", at " ++ showPos p

showEvalError (NonFunctionCalled p func) =
  "value " ++ showValue' 2 func ++ " is used as function, at " ++ showPos p

showEvalError (MatchFailed p subj) =
  "value " ++ showValue' 2 subj ++ " is not mathched, at " ++ showPos p

showEvalError (Expected2Ints p x y) =
  "both arguments should be integers, at " ++ showPos p

showEvalError (OnlyFunctionsCanRecure p) =
  "The value under fixpoint must be a lambda function, at " ++ showPos p

showEvalError (CantCompareFunctions p) =
  "cannot compare with function, at " ++ showPos p

showEvalError (CantCompareValueOfDifferentTypes p x y) =
  "cannot compare " ++ showValue' 2 x ++ " with " ++ showValue' 2 y ++ ", at " ++ showPos p

showEvalError (SameTagDifferInArgCount p t xs ys) =
  "cannot sensibly compare 2 values with the same tag " ++ magenta t ++ " and arg-lists of different sizes "
    ++ "{" ++ intersperse ", " (map (showValue' 2) xs) ++ "} vs {" ++ intersperse ", " (map (showValue' 2) ys) ++ "}"
    ++ ", at " ++ showPos p

showEvalError (UserError p msg v) =
  "user error: " ++ msg ++ " " ++ showValue' 2 v

showEvalError (ReifyError scoped) =
  "during reification: " ++ showScopeError scoped