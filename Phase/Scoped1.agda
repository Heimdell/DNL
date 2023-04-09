
module Phase.Scoped1 where

open import Data.List using (List; _++_; _∷_; []; [_]; map)
open import Data.String using (String) renaming (_++_ to _++s_)
open import Data.Integer using (ℤ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)

open import Position
open import Thinning
-- open import Context

Name : Set
Name = String

data QName : Set where
  ♯   : Name → QName
  _◃_ : Name → QName → QName

Decls : Set
Decls = List QName

data Patᵣ : Set where
  Var    : Name → Patᵣ
  Tagged : Name → List Patᵣ → Patᵣ
  Str    : String → Patᵣ
  Int    : ℤ → Patᵣ
  Wild   : Patᵣ

mutual
  data Exprᵣ : Set where
    Var    : QName → Exprᵣ
    Lam    : List QName → Exprᵣ → Exprᵣ
    Fix    : QName → Exprᵣ → Exprᵣ
    Let    : QName → Exprᵣ → Exprᵣ → Exprᵣ
    LetRec : List (QName × Exprᵣ) → Exprᵣ → Exprᵣ
    App    : Exprᵣ → List Exprᵣ → Exprᵣ
    Int    : ℤ → Exprᵣ
    Str    : String → Exprᵣ
    Tagged : Name → List Exprᵣ → Exprᵣ
    Switch : Exprᵣ → List Altᵣ → Exprᵣ

  record Altᵣ : Set where
    inductive
    constructor Case
    field
      pat  : Patᵣ
      body : Exprᵣ

data Declᵣ : Set where
  Module : Name → List Declᵣ → Declᵣ
  Import : QName → List Name → Declᵣ
  Def    : Name → Exprᵣ → Declᵣ

data Scope : Set where
  Many : List Name → Scope      -- A block of declarations
  _‣_  : Scope → Scope → Scope  -- Adding a parent/ordering
  _◃_  : Name → Scope → Scope   -- Adding

private variable
  c   : Name
  cs  : List Name
  q   : QName
  s t : Scope
  Γ   : List Name

data _⊢_ : Scope → QName → Set where
  Many  : c ∈ Γ → Many Γ ⊢ ♯ c                    -- Var is in a block
  Here  : s ⊢ q → (s ‣ t) ⊢ q                     -- Var is in local scope
  There : t ⊢ q → (s ‣ t) ⊢ q                     -- Var is in parent scope
  _◃_   : (m : Name) → s ⊢ q → (m ◃ s) ⊢ (m ◃ q)  -- Var is in qualified scope

mutual
  -- | Pattern generates the scope to be filled on case-split.
  --
  data Patₛ : Scope → Set where
    Var    : Patₛ (Many [ c ])        -- Declare one var
    Tagged : Name → Patsₛ s → Patₛ s
    Str    : String → Patₛ (Many [])
    Int    : ℤ → Patₛ (Many [])
    Wild   : Patₛ (Many [])

  data Patsₛ : Scope → Set where
    []  : Patsₛ (Many [])
    _∷_ : Patₛ s → Patsₛ t → Patsₛ (t ‣ s)  -- Scopes are composed right-to-left

mutual
  data Exprₛ (s : Scope) : Set where
    Var    : s ⊢ q → Exprₛ s
    Lam    : Exprₛ (Many   cs  ‣ s) → Exprₛ s
    Fix    : Exprₛ (Many [ c ] ‣ s) → Exprₛ s
    Let    : Exprₛ s → Exprₛ (Many [ c ] ‣ s) → Exprₛ s
    LetRec : List (Exprₛ (Many cs ‣ s)) → Exprₛ (Many cs ‣ s) → Exprₛ s
    App    : Exprₛ s → List (Exprₛ s) → Exprₛ s
    Int    : ℤ → Exprₛ s
    Str    : String → Exprₛ s
    Tagged : Name → List (Exprₛ s) → Exprₛ s
    Switch : Exprₛ s → List (Altₛ s) → Exprₛ s

  record Altₛ (s : Scope) : Set where
    inductive
    constructor Case
    field
      scope : Scope
      pat   : Patₛ scope
      body  : Exprₛ (scope ‣ s)  -- Pattern scope is prioritised

-- A module has a name, decls and list of submodules.
--
record Mod : Set where
  inductive
  constructor One
  field
    name : Name
    scope : Scope
    submodules : List Mod

private variable
  M N O : List Mod

-- A path to module, or a module-scope.
--
data ModPath : QName → Scope → List Mod → List Mod → Set where

  -- End of the path, got to the module.
  --
  One  : ModPath (♯ c) s M [ One c s M ]

  -- Look into singleton module
  --
  _◃_  : (m : Name) → ModPath q s M N → ModPath (m ◃ q) (m ◃ s) M [ One m s N ]

  -- Make the singleton module from above.
  --
  thin : M ⊂ N → ModPath q s O M → ModPath q s O N

mutual
  {-
    d = inbound scope
    M = inbound module forest
    s = output scope delta
    N = output module forest delta
  -}
  data Stmtₛ (d : Scope) (M : List Mod) : (s : Scope) (N : List Mod) → Set where
    Module
      : Progₛ d M s N
      → Stmtₛ d M (Many []) [ One c s N ]  -- Add new module, hide the decls

    Import
      : ModPath q s N M
      → Stmtₛ d M s (N ++ M)  -- Dump scope and submodules from imported one

    Decl
      : Exprₛ s
      → Stmtₛ d M (Many [ c ]) []  -- Bring decls into scope

  data Progₛ (d : Scope) (M : List Mod) : (s : Scope) (N : List Mod) → Set where
    End
      : Progₛ d M (Many []) []  -- Do nothing

    _∷_
      : Stmtₛ      d   M       s   N
      → Progₛ (s ‣ d) (N ++ M) t   O  -- Add new scope and modules into the view
      → Progₛ      d   M  (t ‣ s) (O ++ N)  -- Add scopes and modules