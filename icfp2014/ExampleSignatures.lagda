\agdaIgnore{
\begin{code}
module ExampleSignatures where

open import Lib
open import Base
open import TwoLevel
open import Examples hiding (pe0 ; pe1)
\end{code}}
\agdaSnippet\btaPeZeroReturnType{
\begin{code}
pe0 : ∀ {α Δ} → let Γ = map erase Δ in
      AExp Δ α → {!!} → ATInt₀ Γ α
\end{code}}
\agdaIgnore{
\begin{code}
pe0 e ρ = {!!}
\end{code}}
\agdaSnippet\btaPeOneWrong{
\begin{code}
pe1 : ∀ { Δ α } → let Γ = map erase Δ in
         AExp Δ α → AEnv1 Γ Δ → ATInt₁ Γ α
pe1 (SApp f e) ρ    = (pe1 f ρ) (pe1 e ρ)
pe1 (SLam {α} e) ρ  = λ x → {!pe1 e (x ∷ ρ)!} 
\end{code}
}
\agdaIgnore{
\begin{code}
pe1 _ _ = ignore
  where postulate ignore : _
\end{code}}

\agdaSnippet\btaShiftPrime{
\begin{code}
int↑₂ : ∀ {α Γ τ} → ATInt₁ Γ α → ATInt₁ (τ ∷ Γ) α
int↑₂ {D τ}  e = exp↑ e
int↑₂ {SNum} v = v
int↑₂ {SFun α₁ α₂} {Γ} {τ} f = f' 
  where
    f' : ATInt₁ (τ ∷ Γ) α₁ → ATInt₁ (τ ∷ Γ) α₂
    f' x = {!!} 
\end{code}}
