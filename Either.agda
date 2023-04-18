
module Either where

open import Data.Sum
open import Data.Sum using (_⊎_; inj₂; inj₁) public

private variable
  A B E : Set

pure : A → A ⊎ E
pure = inj₁

fail : E → A ⊎ E
fail = inj₂

open import Function

_>>=_ : A ⊎ E → (A → B ⊎ E) → B ⊎ E
inj₁ x >>= k = k x
inj₂ y >>= k = inj₂ y

_<*>_ : (A → B) ⊎ E → A ⊎ E → B ⊎ E
inj₁ x <*> inj₁ x₁ = inj₁ (x x₁)
inj₁ x <*> inj₂ y = inj₂ y
inj₂ y <*> inj₁ x = inj₂ y
inj₂ y <*> inj₂ y₁ = inj₂ y

_<!>_ :  A ⊎ E → (E → B) → A ⊎ B
ma <!> f = [ pure , fail ∘ f ] ma

open import Data.List

each : (A → B ⊎ E) → List A → List B ⊎ E
each f []       = ⦇ [] ⦈
each f (x ∷ xs) = ⦇ f x ∷ each f xs ⦈