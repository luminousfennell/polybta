\agdaIgnore{
\begin{code}
module TwoLevel where
open import Lib
open import Base
\end{code}}

\agdaSnippet\btaAType{
\begin{code}
data AType : Set where
  SNum  : AType
  SFun  : AType → AType → AType
  D     : Type → AType

ACtx = List AType
\end{code}}
\agdaIgnore{
\begin{code}
-- The mapping from annotated types to residual types is straightforward.
erase : AType → Type
erase SNum = Num
erase (SFun α₁ α₂) = Fun (erase α₁) (erase α₂)
erase (D x) = x
\end{code}}
\agdaIgnore{
\begin{code}
  -- It is easy to check that the stratification respects the
  -- well-formedness, given the intended mapping from ATypes to
  -- binding times expained above:


-- The typed annotated terms: The binding times of variables is
-- determined by the corresponding type-binding in the context. In the
-- other cases, the A- and D-prefixes on term constructors inidicate
-- the corresponding binding times for the resulting terms.
\end{code}}
\agdaSnippet\btaAExp{
\begin{code}
data AExp (Δ : ACtx) : AType → Set where
  Var : ∀ {α} → α ∈ Δ → AExp Δ α
  SCst : ℕ → AExp Δ SNum
  SAdd : AExp Δ SNum → AExp Δ SNum → AExp Δ SNum
  SLam : ∀ {α₁ α₂} → AExp (α₁ ∷ Δ) α₂ → AExp Δ (SFun α₁ α₂)
  SApp : ∀ {α₁ α₂} → AExp Δ (SFun α₁ α₂) → AExp Δ α₁ → AExp Δ α₂
  DCst : ℕ → AExp Δ (D Num)
  DAdd : AExp Δ (D Num) → AExp Δ (D Num) → AExp Δ (D Num)
  DLam : ∀ {σ₁ σ₂} → AExp ((D σ₁) ∷ Δ) (D σ₂) → AExp Δ (D (Fun σ₁ σ₂))
  DApp : ∀ {σ₁ σ₂} → AExp Δ (D (Fun σ₂ σ₁)) → AExp Δ (D σ₂) → AExp Δ (D σ₁)
  Lift : AExp Δ SNum → AExp Δ (D Num)
\end{code}}
\agdaIgnore{
\begin{code}
-- The terms of AExp assign a binding time to each subterm. For
-- program specialization, we interpret terms with dynamic binding
-- time as the programs subject to specialization, and their subterms
-- with static binding time as statically known inputs. A partial
-- evaluation function (or specializer) then compiles the program into
-- a residual term for that is specialized for the static inputs. The
-- main complication when defining partial evaluation as a total,
-- primitively recursive function will be the treatment of the De
-- Bruijn variables of non-closed residual expressions.

-- Before diving into the precise definition, it is instructive to
-- investigate the expected result of partial evaluation on some
-- examples.

-- Utilities to define partial functions
\end{code}}
