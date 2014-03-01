\agdaIgnore{
\begin{code}
module CtxExtension where
open import Lib
-- Extension of lists at the front and, as a generalization, extension
-- of lists somewhere in the middle.

-- Extension of a list by consing elements at the front. 
\end{code}}
\agdaSnippet\btaExtend{
\begin{code}
data _↝_ {A : Set} : List A → List A → Set where
  refl   : ∀ {Γ}      → Γ ↝ Γ
  extend : ∀ {Γ Γ' τ} → Γ ↝ Γ' → Γ ↝ (τ ∷ Γ')

_⊕_ : ∀ {A : Set}{Γ Γ' Γ'' : List A} → 
    Γ ↝ Γ' → Γ' ↝ Γ'' → Γ ↝ Γ''
_⊕_ Γ↝Γ' refl = Γ↝Γ'                                 
_⊕_ Γ↝Γ' (extend Γ'↝Γ'') = extend (Γ↝Γ' ⊕ Γ'↝Γ'')
\end{code}}
\agdaIgnore{
\begin{code}

-- Of course, refl is the identity for combining two extensions.
lem-refl-id : ∀ {A : Set} {Γ Γ' : List A} →
                  (Γ↝Γ' : Γ ↝ Γ') →
                  Γ↝Γ' ≡ (refl ⊕ Γ↝Γ')  
lem-refl-id refl = refl
lem-refl-id (extend Γ↝Γ') =
  cong extend (lem-refl-id Γ↝Γ')
-- TODO: why does this work?
-- lem-refl-id (extend Γ↝Γ') = lem-refl-id (extend Γ↝Γ')

-- Extending a list in the middle: 
data _↝_↝_ {A : Set} : List A → List A → List A → Set where
  -- First prepend the extension list to the common suffix
  refl   : ∀ {Γ Γ''} → Γ ↝ Γ'' → Γ ↝ [] ↝ Γ'' 
  -- ... and then add the common prefix
  extend : ∀ {Γ Γ' Γ'' τ} →
               Γ ↝ Γ' ↝ Γ'' → (τ ∷ Γ) ↝ (τ ∷ Γ') ↝ (τ ∷ Γ'') 
\end{code}}
