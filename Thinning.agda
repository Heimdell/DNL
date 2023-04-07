
module Thinning where

open import Data.List

private variable
  A     : Set
  u v w : List A
  a     : A

-- | Variable selection, a bitmask.
--
data _⊂_ : (u v : List A) → Set where
  ε  : _⊂_ {A = A} [] []          -- empty
  𝟘∷ : u ⊂ v → u ⊂ (a ∷ v)       -- keep var
  𝟙∷ : u ⊂ v → (a ∷ u) ⊂ (a ∷ v) -- drop var

_∈_ : A → List A → Set
a ∈ as = [ a ] ⊂ as

infix 3 _⊂_ _∈_

-- | Ignore top var.
--
weaken : (a ∷ u) ⊂ v → u ⊂ v
weaken (𝟘∷ uv) = 𝟘∷ (weaken uv)
weaken (𝟙∷ uv) = 𝟘∷ uv

-- | Compose variable selections.
--
_∙_ : u ⊂ v → v ⊂ w → u ⊂ w
ε     ∙    vw = vw
𝟘∷ uv ∙ 𝟘∷ vw = uv ∙ 𝟘∷ (weaken vw)
𝟘∷ uv ∙ 𝟙∷ vw = 𝟘∷ (uv ∙ vw)
𝟙∷ uv ∙ 𝟘∷ vw = 𝟘∷ (𝟙∷ uv ∙ vw)
𝟙∷ uv ∙ 𝟙∷ vw = 𝟙∷ (uv ∙ vw)

-- | Bitmask of zeros (no variable is taken).
--
𝟘⋯ : [] ⊂ v
𝟘⋯ {v = []} = ε
𝟘⋯ {v = x ∷ v} = 𝟘∷ 𝟘⋯

-- | Bitmask of ones (all variables are taken).
--
𝟙⋯ : v ⊂ v
𝟙⋯ {v = []} = ε
𝟙⋯ {v = x ∷ v} = 𝟙∷ 𝟙⋯