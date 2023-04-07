{-# OPTIONS --guardedness #-}

module Prog where

open import Data.Unit.Polymorphic using (⊤; tt)
open import Lisp.Grammar.ParserLisp using (Err; ok; bad; parseStmt; parseStart)
open import Lisp.Grammar.ASTLisp hiding (String)
open import IO
open import System.Environment

open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Integer using (_+_)
open import Data.String using (String) renaming (_++_ to _++s_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; subst)
open import Function using (_∘_; case_of_)

open import Phase.Raw
open import Phase.Scoped
open import Phase.Evaluated
open import Pass.FromBNFC
open import Pass.ToScoped
open import Pass.Evaluate
open import Position
open import Name
open import Pretty

showCtx : {Δ : _} → Ctx Δ → String
showCtx {[]} [] = "--"
showCtx {x ∷ Δ} (px ∷ ctx) = showName x ++s " = " ++s showValue' 2 px ++s "\n" ++s showCtx ctx


rewr : {Γ Δ : _} → {n : Name.Name} → Δ ++ n ∷ Γ ≡ (Δ ++ [ n ]) ++ Γ
rewr {Δ = []} = refl
rewr {Δ = x ∷ Δ} = cong₂ _∷_ refl (rewr {Δ = Δ})


Mem : List Name.Name → Set
Mem Γ = All (λ _ → Exprᵣ) Γ


logError : String → String → IO {a = Agda.Primitive.lzero} ⊤
logError system msg = putStrLn (br (red system) ++s ": " ++s msg)


logSuccess : String → String → IO {a = Agda.Primitive.lzero} ⊤
logSuccess system msg = putStrLn (br (green system) ++s ": " ++s msg)


logMsg : String → IO {a = Agda.Primitive.lzero} ⊤
logMsg system = putStrLn (br (yellow system))


prepare : {A : Set} {Γ : List Name.Name} → Exprᵣ → Ctx Γ → IO A → (Value → IO A) → IO A
prepare {Γ = Γ} expr stack nope yep = do
  case checkₛ {Γ = Γ} expr of λ where
    (inj₂ err) → do
      logError "SCOPE" (showScopeError err)
      nope

    (inj₁ res) → do
      case eval stack res of λ where
        (inj₂ err) → do
          logError "EVAL" (showEvalError err)
          nope

        (inj₁ value) → do
          yep value


unfold : {Γ : _} → Exprᵣ → Ctx Γ → IO (∃[ Δ ] Ctx (Δ ++ Γ))
unfold {Γ} (Let p n expr body) stack = do
  prepare expr stack (do pure ([] , stack)) λ where
    value → do
      logSuccess ("ADDED") (showName n ++s br " = " ++s showValue value)
      Δ , stack ← unfold {Γ = n ∷ Γ} body (value ∷ stack)
      pure (Δ ++ [ n ] , subst Ctx rewr stack)

unfold {Γ} expr stack = do
  prepare expr stack (do pure ([] , stack)) λ where
    value → do
      logSuccess "RESULT" (showValue value)
      pure ([] , stack)


{-# TERMINATING #-}
repl : {Δ : _} → Ctx Δ → IO ⊤
repl {Δ} stack = do
  logMsg "\nCOMMAND?"
  line ← getLine
  case parseStmt line of λ where
    (bad err) → do
      logError "PARSE" (Data.String.fromList err)
      repl stack

    (ok (decl p (name x) expr)) → do
      prepare (exprᵣ expr) stack (repl stack) λ where
        value → do
          logSuccess ("ADDED") (showName (♯ x) ++s br " = " ++s showValue value)
          repl {Δ = ♯ x ∷ Δ} (value ∷ stack)

    (ok (listAll p)) → do
      putStrLn (showCtx stack)
      repl stack

    (ok (perform p expr)) → do
      prepare (exprᵣ expr) stack (repl stack) λ where
        value → do
          logSuccess "RESULT" (showValue value)
          repl stack

    (ok (load p file)) → do
      let file = Data.String.fromList file
      txt ← readFiniteFile file
      case parseStart txt of λ where
        (bad err) → do
          logError "PARSE" (Data.String.fromList err)
          repl stack

        (ok (s _ expr)) → do
          let expr = exprᵣ expr
          putStrLn (showExprᵣ expr)
          putStrLn ""
          _ , stack ← unfold expr stack
          logSuccess "LOADED" (showValue (Str file))
          repl stack


import Agda.Builtin.IO

open import Stdlib

main : Agda.Builtin.IO.IO ⊤
main = run do
  logMsg "\n   DNL (Definitely Not Lisp) REPL, v0.1"
  repl {Δ = ♯ "add"  ∷ ♯ "compare" ∷ []}
            (Lam add ∷ Lam cmp     ∷ [])
