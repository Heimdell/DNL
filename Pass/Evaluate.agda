
module Pass.Evaluate where

open import Data.List using (List; _++_; _∷_; [])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.String using ()
open import Data.Integer using ()
open import Relation.Nullary using (yes; no)

open import Name
open import Thinning using (_∈_; 𝟙∷; 𝟘∷)
open import Either
open import Position

open import Phase.Scoped
open import Phase.Evaluated

private variable
  Γ Δ : List Name
  n   : Name

_<>_ : Ctx Δ → Ctx Γ → Ctx (Δ ++ Γ)
_<>_ {Δ = []}     []            stack = stack
_<>_ {Δ = _ ∷ _} (value ∷ args) stack = value ∷ args <> stack


pick : Ctx Γ → n ∈ Γ → Value
pick (_     ∷ stack) (𝟘∷ ptr) = pick stack ptr
pick (value ∷ _)     (𝟙∷ _)   = value


toList : Ctx Γ → List Value
toList []            = []
toList (value ∷ ctx) = value ∷ toList ctx

open import Function
open import Data.Maybe using (Maybe; just; nothing)

init : Ctx Δ
init {Δ = []}    = []
init {Δ = _ ∷ _} = Tagged "Nil" [] ∷ init


write : Value → n ∈ Γ → All (λ _ -> Value) Γ → All (λ _ -> Value) Γ
write what (𝟘∷ ptr) (value ∷ stack) = value ∷ write what ptr stack
write what (𝟙∷ ptr) (_     ∷ stack) = what  ∷ stack

mutual
  pat : Patₛ Δ → Value → Ctx Δ → Maybe (Ctx Δ)
  pat (Tagged p ctor xs) (Tagged ctor₁ ys) acc with ctor Data.String.≟ ctor₁
  ... | yes _ = pats xs ys acc
  ... | no  _ = nothing
  pat (Var p x) val acc = just (write val x acc)
  pat (Int p x) (Int y) acc with x Data.Integer.≟ y
  ... | yes _ = just acc
  ... | no  _ = nothing
  pat (Str p x) (Str y) acc with x Data.String.≟ y
  ... | yes _ = just acc
  ... | no  _ = nothing
  pat (Wild p) _ acc = just acc
  pat _ _ _   = nothing


  pats : List (Patₛ Δ) → List Value → Ctx Δ → Maybe (Ctx Δ)
  pats [] [] acc = just acc
  pats [] (x ∷ vs) acc = nothing
  pats (x ∷ ps) [] acc = nothing
  pats (x ∷ ps) (x₁ ∷ vs) acc with pat x x₁ acc
  ... | just acc = pats ps vs acc
  ... | nothing  = nothing

mutual
  {-# TERMINATING #-}
  eval : Ctx Γ → Exprₛ Γ → Value ⊎ EvalError
  eval stack (Var p x) = pure (pick stack x)
  eval stack (Lam p expr) = pure (Lam λ p args → eval (args <> stack) expr)
  eval stack (App p f xs) = do
    f  ← eval     stack f
    xs ← evalList stack xs
    apply p f xs

  eval stack (Let p expr expr₁) = do
    val ← eval stack expr
    eval (val ∷ stack) expr₁

  eval stack (Fix p lam@(Lam {Δ = Δ} _ _)) = do
    let
      fixpoint = Lam {Δ} λ p xs → do
        f ← eval stack (Fix p lam)
        apply p f (toList xs)

    eval (fixpoint ∷ stack) lam  -- fix lam ==> lam (\ xs -> fix lam xs)

  eval stack (Fix p e) = fail (OnlyFunctionsCanRecure p)

  eval stack (Int p x) = pure (Int x)
  eval stack (Str p x) = pure (Str x)
  eval stack (Tagged p x xs) = ⦇ (Tagged x) (evalList stack xs) ⦈
  eval stack (Match p expr alts) = do
    value ← eval stack expr
    match p stack value alts


  alt : Ctx Γ → Value → Altₛ Γ → Maybe Value ⊎ EvalError
  alt stack expr (Case p pat₁ body)
    with pat pat₁ expr init
  ... | just delta = do
        res ← eval (delta <> stack) body
        pure (just res)

  ... | nothing = pure nothing


  match : (p : Pos) → Ctx Γ → Value → List (Altₛ Γ) → Value ⊎ EvalError
  match p stack subj [] = fail (MatchFailed p subj)
  match p stack subj (alt₁ ∷ alts) = do
    res ← alt stack subj alt₁
    case res of λ where
      (just res) → pure res
      nothing    → match p stack subj alts


  evalList : Ctx Γ → List (Exprₛ Γ) → List Value ⊎ EvalError
  evalList _     []       = ⦇ [] ⦈
  evalList stack (x ∷ xs) = ⦇ eval stack x ∷ evalList stack xs ⦈


  pack
    : Pos
    → Ctx Γ
    → List Value
    → Ctx (Δ ++ Γ)
    ⊎ EvalError
  pack {Δ = []}        p stack [] = pure stack
  pack {Δ = []}        p stack xs = fail (TooMuchArgs   p [] xs)
  pack {Δ = Δ@(_ ∷ _)} p stack [] = fail (NotEnoughArgs p Δ  [])

  pack {Δ = x ∷ Δ} p stack (x₁ ∷ xs) = do
    res ← pack p stack xs
    pure (x₁ ∷ res)


  fromList
    : Pos
    → List Value
    → Ctx Δ
    ⊎ EvalError
  fromList {Δ = []}        p [] = pure []
  fromList {Δ = []}        p xs = fail (TooMuchArgs   p [] xs)
  fromList {Δ = Δ@(_ ∷ _)} p [] = fail (NotEnoughArgs p Δ  [])

  fromList {Δ = x ∷ Δ} p (x₁ ∷ xs) = do
    res ← fromList p xs
    pure (x₁ ∷ res)


  apply : Pos → Value → List Value → Value ⊎ EvalError
  apply p (Lam {Δ = Δ} k) xs = do
    stack ← case fromList p xs of λ where
      (inj₂ (TooMuchArgs   _ _ _)) → fail (TooMuchArgs   p Δ xs)
      (inj₂ (NotEnoughArgs _ _ _)) → fail (NotEnoughArgs p Δ xs)
      other                      → other

    k p stack

  apply p (Int    x)    xs = fail (NonFunctionCalled p (Int x))
  apply p (Str    x)    xs = fail (NonFunctionCalled p (Str x))
  apply p (Tagged x x₁) xs = fail (NonFunctionCalled p (Tagged x x₁))